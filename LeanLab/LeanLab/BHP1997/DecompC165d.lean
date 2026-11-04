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

/- Page 51. Exact E2 grid certificate, kernel checked row by row.
The 512 leading rows are empty. `lowerTwo_row_peel` exposes one row at a time so that each
row sum is decided once and the assembly stays a numeral sum. -/
private theorem lowerTwo_row_peel (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), ∑ j ∈ Finset.range 4096, lowerTwoGridWeight i j) =
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight i j)
        + (∑ j ∈ Finset.range 4096, lowerTwoGridWeight n j) := by
  rw [Finset.sum_range_succ]

private theorem lowerTwo_row_0 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 0 j) = 0 := by decide
private theorem lowerTwo_row_1 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1 j) = 0 := by decide
private theorem lowerTwo_row_2 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2 j) = 0 := by decide
private theorem lowerTwo_row_3 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3 j) = 0 := by decide
private theorem lowerTwo_row_4 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4 j) = 0 := by decide
private theorem lowerTwo_row_5 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 5 j) = 0 := by decide
private theorem lowerTwo_row_6 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 6 j) = 0 := by decide
private theorem lowerTwo_row_7 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 7 j) = 0 := by decide
private theorem lowerTwo_row_8 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 8 j) = 0 := by decide
private theorem lowerTwo_row_9 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 9 j) = 0 := by decide
private theorem lowerTwo_row_10 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 10 j) = 0 := by decide
private theorem lowerTwo_row_11 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 11 j) = 0 := by decide
private theorem lowerTwo_row_12 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 12 j) = 0 := by decide
private theorem lowerTwo_row_13 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 13 j) = 0 := by decide
private theorem lowerTwo_row_14 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 14 j) = 0 := by decide
private theorem lowerTwo_row_15 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 15 j) = 0 := by decide
private theorem lowerTwo_row_16 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 16 j) = 0 := by decide
private theorem lowerTwo_row_17 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 17 j) = 0 := by decide
private theorem lowerTwo_row_18 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 18 j) = 0 := by decide
private theorem lowerTwo_row_19 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 19 j) = 0 := by decide
private theorem lowerTwo_row_20 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 20 j) = 0 := by decide
private theorem lowerTwo_row_21 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 21 j) = 0 := by decide
private theorem lowerTwo_row_22 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 22 j) = 0 := by decide
private theorem lowerTwo_row_23 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 23 j) = 0 := by decide
private theorem lowerTwo_row_24 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 24 j) = 0 := by decide
private theorem lowerTwo_row_25 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 25 j) = 0 := by decide
private theorem lowerTwo_row_26 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 26 j) = 0 := by decide
private theorem lowerTwo_row_27 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 27 j) = 0 := by decide
private theorem lowerTwo_row_28 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 28 j) = 0 := by decide
private theorem lowerTwo_row_29 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 29 j) = 0 := by decide
private theorem lowerTwo_row_30 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 30 j) = 0 := by decide
private theorem lowerTwo_row_31 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 31 j) = 0 := by decide
private theorem lowerTwo_row_32 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 32 j) = 0 := by decide
private theorem lowerTwo_row_33 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 33 j) = 0 := by decide
private theorem lowerTwo_row_34 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 34 j) = 0 := by decide
private theorem lowerTwo_row_35 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 35 j) = 0 := by decide
private theorem lowerTwo_row_36 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 36 j) = 0 := by decide
private theorem lowerTwo_row_37 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 37 j) = 0 := by decide
private theorem lowerTwo_row_38 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 38 j) = 0 := by decide
private theorem lowerTwo_row_39 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 39 j) = 0 := by decide
private theorem lowerTwo_row_40 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 40 j) = 0 := by decide
private theorem lowerTwo_row_41 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 41 j) = 0 := by decide
private theorem lowerTwo_row_42 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 42 j) = 0 := by decide
private theorem lowerTwo_row_43 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 43 j) = 0 := by decide
private theorem lowerTwo_row_44 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 44 j) = 0 := by decide
private theorem lowerTwo_row_45 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 45 j) = 0 := by decide
private theorem lowerTwo_row_46 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 46 j) = 0 := by decide
private theorem lowerTwo_row_47 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 47 j) = 0 := by decide
private theorem lowerTwo_row_48 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 48 j) = 0 := by decide
private theorem lowerTwo_row_49 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 49 j) = 0 := by decide
private theorem lowerTwo_row_50 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 50 j) = 0 := by decide
private theorem lowerTwo_row_51 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 51 j) = 0 := by decide
private theorem lowerTwo_row_52 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 52 j) = 0 := by decide
private theorem lowerTwo_row_53 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 53 j) = 0 := by decide
private theorem lowerTwo_row_54 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 54 j) = 0 := by decide
private theorem lowerTwo_row_55 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 55 j) = 0 := by decide
private theorem lowerTwo_row_56 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 56 j) = 0 := by decide
private theorem lowerTwo_row_57 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 57 j) = 0 := by decide
private theorem lowerTwo_row_58 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 58 j) = 0 := by decide
private theorem lowerTwo_row_59 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 59 j) = 0 := by decide
private theorem lowerTwo_row_60 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 60 j) = 0 := by decide
private theorem lowerTwo_row_61 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 61 j) = 0 := by decide
private theorem lowerTwo_row_62 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 62 j) = 0 := by decide
private theorem lowerTwo_row_63 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 63 j) = 0 := by decide
private theorem lowerTwo_row_64 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 64 j) = 0 := by decide
private theorem lowerTwo_row_65 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 65 j) = 0 := by decide
private theorem lowerTwo_row_66 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 66 j) = 0 := by decide
private theorem lowerTwo_row_67 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 67 j) = 0 := by decide
private theorem lowerTwo_row_68 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 68 j) = 0 := by decide
private theorem lowerTwo_row_69 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 69 j) = 0 := by decide
private theorem lowerTwo_row_70 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 70 j) = 0 := by decide
private theorem lowerTwo_row_71 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 71 j) = 0 := by decide
private theorem lowerTwo_row_72 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 72 j) = 0 := by decide
private theorem lowerTwo_row_73 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 73 j) = 0 := by decide
private theorem lowerTwo_row_74 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 74 j) = 0 := by decide
private theorem lowerTwo_row_75 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 75 j) = 0 := by decide
private theorem lowerTwo_row_76 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 76 j) = 0 := by decide
private theorem lowerTwo_row_77 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 77 j) = 0 := by decide
private theorem lowerTwo_row_78 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 78 j) = 0 := by decide
private theorem lowerTwo_row_79 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 79 j) = 0 := by decide
private theorem lowerTwo_row_80 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 80 j) = 0 := by decide
private theorem lowerTwo_row_81 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 81 j) = 0 := by decide
private theorem lowerTwo_row_82 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 82 j) = 0 := by decide
private theorem lowerTwo_row_83 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 83 j) = 0 := by decide
private theorem lowerTwo_row_84 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 84 j) = 0 := by decide
private theorem lowerTwo_row_85 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 85 j) = 0 := by decide
private theorem lowerTwo_row_86 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 86 j) = 0 := by decide
private theorem lowerTwo_row_87 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 87 j) = 0 := by decide
private theorem lowerTwo_row_88 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 88 j) = 0 := by decide
private theorem lowerTwo_row_89 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 89 j) = 0 := by decide
private theorem lowerTwo_row_90 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 90 j) = 0 := by decide
private theorem lowerTwo_row_91 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 91 j) = 0 := by decide
private theorem lowerTwo_row_92 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 92 j) = 0 := by decide
private theorem lowerTwo_row_93 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 93 j) = 0 := by decide
private theorem lowerTwo_row_94 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 94 j) = 0 := by decide
private theorem lowerTwo_row_95 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 95 j) = 0 := by decide
private theorem lowerTwo_row_96 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 96 j) = 0 := by decide
private theorem lowerTwo_row_97 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 97 j) = 0 := by decide
private theorem lowerTwo_row_98 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 98 j) = 0 := by decide
private theorem lowerTwo_row_99 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 99 j) = 0 := by decide
private theorem lowerTwo_row_100 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 100 j) = 0 := by decide
private theorem lowerTwo_row_101 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 101 j) = 0 := by decide
private theorem lowerTwo_row_102 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 102 j) = 0 := by decide
private theorem lowerTwo_row_103 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 103 j) = 0 := by decide
private theorem lowerTwo_row_104 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 104 j) = 0 := by decide
private theorem lowerTwo_row_105 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 105 j) = 0 := by decide
private theorem lowerTwo_row_106 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 106 j) = 0 := by decide
private theorem lowerTwo_row_107 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 107 j) = 0 := by decide
private theorem lowerTwo_row_108 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 108 j) = 0 := by decide
private theorem lowerTwo_row_109 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 109 j) = 0 := by decide
private theorem lowerTwo_row_110 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 110 j) = 0 := by decide
private theorem lowerTwo_row_111 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 111 j) = 0 := by decide
private theorem lowerTwo_row_112 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 112 j) = 0 := by decide
private theorem lowerTwo_row_113 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 113 j) = 0 := by decide
private theorem lowerTwo_row_114 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 114 j) = 0 := by decide
private theorem lowerTwo_row_115 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 115 j) = 0 := by decide
private theorem lowerTwo_row_116 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 116 j) = 0 := by decide
private theorem lowerTwo_row_117 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 117 j) = 0 := by decide
private theorem lowerTwo_row_118 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 118 j) = 0 := by decide
private theorem lowerTwo_row_119 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 119 j) = 0 := by decide
private theorem lowerTwo_row_120 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 120 j) = 0 := by decide
private theorem lowerTwo_row_121 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 121 j) = 0 := by decide
private theorem lowerTwo_row_122 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 122 j) = 0 := by decide
private theorem lowerTwo_row_123 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 123 j) = 0 := by decide
private theorem lowerTwo_row_124 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 124 j) = 0 := by decide
private theorem lowerTwo_row_125 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 125 j) = 0 := by decide
private theorem lowerTwo_row_126 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 126 j) = 0 := by decide
private theorem lowerTwo_row_127 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 127 j) = 0 := by decide
private theorem lowerTwo_row_128 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 128 j) = 0 := by decide
private theorem lowerTwo_row_129 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 129 j) = 0 := by decide
private theorem lowerTwo_row_130 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 130 j) = 0 := by decide
private theorem lowerTwo_row_131 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 131 j) = 0 := by decide
private theorem lowerTwo_row_132 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 132 j) = 0 := by decide
private theorem lowerTwo_row_133 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 133 j) = 0 := by decide
private theorem lowerTwo_row_134 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 134 j) = 0 := by decide
private theorem lowerTwo_row_135 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 135 j) = 0 := by decide
private theorem lowerTwo_row_136 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 136 j) = 0 := by decide
private theorem lowerTwo_row_137 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 137 j) = 0 := by decide
private theorem lowerTwo_row_138 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 138 j) = 0 := by decide
private theorem lowerTwo_row_139 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 139 j) = 0 := by decide
private theorem lowerTwo_row_140 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 140 j) = 0 := by decide
private theorem lowerTwo_row_141 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 141 j) = 0 := by decide
private theorem lowerTwo_row_142 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 142 j) = 0 := by decide
private theorem lowerTwo_row_143 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 143 j) = 0 := by decide
private theorem lowerTwo_row_144 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 144 j) = 0 := by decide
private theorem lowerTwo_row_145 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 145 j) = 0 := by decide
private theorem lowerTwo_row_146 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 146 j) = 0 := by decide
private theorem lowerTwo_row_147 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 147 j) = 0 := by decide
private theorem lowerTwo_row_148 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 148 j) = 0 := by decide
private theorem lowerTwo_row_149 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 149 j) = 0 := by decide
private theorem lowerTwo_row_150 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 150 j) = 0 := by decide
private theorem lowerTwo_row_151 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 151 j) = 0 := by decide
private theorem lowerTwo_row_152 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 152 j) = 0 := by decide
private theorem lowerTwo_row_153 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 153 j) = 0 := by decide
private theorem lowerTwo_row_154 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 154 j) = 0 := by decide
private theorem lowerTwo_row_155 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 155 j) = 0 := by decide
private theorem lowerTwo_row_156 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 156 j) = 0 := by decide
private theorem lowerTwo_row_157 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 157 j) = 0 := by decide
private theorem lowerTwo_row_158 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 158 j) = 0 := by decide
private theorem lowerTwo_row_159 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 159 j) = 0 := by decide
private theorem lowerTwo_row_160 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 160 j) = 0 := by decide
private theorem lowerTwo_row_161 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 161 j) = 0 := by decide
private theorem lowerTwo_row_162 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 162 j) = 0 := by decide
private theorem lowerTwo_row_163 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 163 j) = 0 := by decide
private theorem lowerTwo_row_164 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 164 j) = 0 := by decide
private theorem lowerTwo_row_165 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 165 j) = 0 := by decide
private theorem lowerTwo_row_166 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 166 j) = 0 := by decide
private theorem lowerTwo_row_167 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 167 j) = 0 := by decide
private theorem lowerTwo_row_168 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 168 j) = 0 := by decide
private theorem lowerTwo_row_169 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 169 j) = 0 := by decide
private theorem lowerTwo_row_170 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 170 j) = 0 := by decide
private theorem lowerTwo_row_171 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 171 j) = 0 := by decide
private theorem lowerTwo_row_172 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 172 j) = 0 := by decide
private theorem lowerTwo_row_173 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 173 j) = 0 := by decide
private theorem lowerTwo_row_174 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 174 j) = 0 := by decide
private theorem lowerTwo_row_175 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 175 j) = 0 := by decide
private theorem lowerTwo_row_176 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 176 j) = 0 := by decide
private theorem lowerTwo_row_177 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 177 j) = 0 := by decide
private theorem lowerTwo_row_178 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 178 j) = 0 := by decide
private theorem lowerTwo_row_179 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 179 j) = 0 := by decide
private theorem lowerTwo_row_180 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 180 j) = 0 := by decide
private theorem lowerTwo_row_181 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 181 j) = 0 := by decide
private theorem lowerTwo_row_182 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 182 j) = 0 := by decide
private theorem lowerTwo_row_183 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 183 j) = 0 := by decide
private theorem lowerTwo_row_184 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 184 j) = 0 := by decide
private theorem lowerTwo_row_185 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 185 j) = 0 := by decide
private theorem lowerTwo_row_186 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 186 j) = 0 := by decide
private theorem lowerTwo_row_187 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 187 j) = 0 := by decide
private theorem lowerTwo_row_188 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 188 j) = 0 := by decide
private theorem lowerTwo_row_189 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 189 j) = 0 := by decide
private theorem lowerTwo_row_190 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 190 j) = 0 := by decide
private theorem lowerTwo_row_191 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 191 j) = 0 := by decide
private theorem lowerTwo_row_192 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 192 j) = 0 := by decide
private theorem lowerTwo_row_193 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 193 j) = 0 := by decide
private theorem lowerTwo_row_194 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 194 j) = 0 := by decide
private theorem lowerTwo_row_195 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 195 j) = 0 := by decide
private theorem lowerTwo_row_196 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 196 j) = 0 := by decide
private theorem lowerTwo_row_197 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 197 j) = 0 := by decide
private theorem lowerTwo_row_198 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 198 j) = 0 := by decide
private theorem lowerTwo_row_199 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 199 j) = 0 := by decide
private theorem lowerTwo_row_200 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 200 j) = 0 := by decide
private theorem lowerTwo_row_201 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 201 j) = 0 := by decide
private theorem lowerTwo_row_202 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 202 j) = 0 := by decide
private theorem lowerTwo_row_203 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 203 j) = 0 := by decide
private theorem lowerTwo_row_204 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 204 j) = 0 := by decide
private theorem lowerTwo_row_205 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 205 j) = 0 := by decide
private theorem lowerTwo_row_206 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 206 j) = 0 := by decide
private theorem lowerTwo_row_207 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 207 j) = 0 := by decide
private theorem lowerTwo_row_208 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 208 j) = 0 := by decide
private theorem lowerTwo_row_209 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 209 j) = 0 := by decide
private theorem lowerTwo_row_210 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 210 j) = 0 := by decide
private theorem lowerTwo_row_211 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 211 j) = 0 := by decide
private theorem lowerTwo_row_212 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 212 j) = 0 := by decide
private theorem lowerTwo_row_213 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 213 j) = 0 := by decide
private theorem lowerTwo_row_214 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 214 j) = 0 := by decide
private theorem lowerTwo_row_215 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 215 j) = 0 := by decide
private theorem lowerTwo_row_216 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 216 j) = 0 := by decide
private theorem lowerTwo_row_217 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 217 j) = 0 := by decide
private theorem lowerTwo_row_218 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 218 j) = 0 := by decide
private theorem lowerTwo_row_219 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 219 j) = 0 := by decide
private theorem lowerTwo_row_220 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 220 j) = 0 := by decide
private theorem lowerTwo_row_221 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 221 j) = 0 := by decide
private theorem lowerTwo_row_222 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 222 j) = 0 := by decide
private theorem lowerTwo_row_223 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 223 j) = 0 := by decide
private theorem lowerTwo_row_224 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 224 j) = 0 := by decide
private theorem lowerTwo_row_225 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 225 j) = 0 := by decide
private theorem lowerTwo_row_226 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 226 j) = 0 := by decide
private theorem lowerTwo_row_227 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 227 j) = 0 := by decide
private theorem lowerTwo_row_228 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 228 j) = 0 := by decide
private theorem lowerTwo_row_229 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 229 j) = 0 := by decide
private theorem lowerTwo_row_230 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 230 j) = 0 := by decide
private theorem lowerTwo_row_231 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 231 j) = 0 := by decide
private theorem lowerTwo_row_232 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 232 j) = 0 := by decide
private theorem lowerTwo_row_233 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 233 j) = 0 := by decide
private theorem lowerTwo_row_234 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 234 j) = 0 := by decide
private theorem lowerTwo_row_235 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 235 j) = 0 := by decide
private theorem lowerTwo_row_236 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 236 j) = 0 := by decide
private theorem lowerTwo_row_237 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 237 j) = 0 := by decide
private theorem lowerTwo_row_238 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 238 j) = 0 := by decide
private theorem lowerTwo_row_239 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 239 j) = 0 := by decide
private theorem lowerTwo_row_240 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 240 j) = 0 := by decide
private theorem lowerTwo_row_241 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 241 j) = 0 := by decide
private theorem lowerTwo_row_242 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 242 j) = 0 := by decide
private theorem lowerTwo_row_243 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 243 j) = 0 := by decide
private theorem lowerTwo_row_244 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 244 j) = 0 := by decide
private theorem lowerTwo_row_245 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 245 j) = 0 := by decide
private theorem lowerTwo_row_246 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 246 j) = 0 := by decide
private theorem lowerTwo_row_247 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 247 j) = 0 := by decide
private theorem lowerTwo_row_248 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 248 j) = 0 := by decide
private theorem lowerTwo_row_249 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 249 j) = 0 := by decide
private theorem lowerTwo_row_250 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 250 j) = 0 := by decide
private theorem lowerTwo_row_251 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 251 j) = 0 := by decide
private theorem lowerTwo_row_252 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 252 j) = 0 := by decide
private theorem lowerTwo_row_253 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 253 j) = 0 := by decide
private theorem lowerTwo_row_254 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 254 j) = 0 := by decide
private theorem lowerTwo_row_255 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 255 j) = 0 := by decide
private theorem lowerTwo_row_256 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 256 j) = 0 := by decide
private theorem lowerTwo_row_257 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 257 j) = 0 := by decide
private theorem lowerTwo_row_258 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 258 j) = 0 := by decide
private theorem lowerTwo_row_259 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 259 j) = 0 := by decide
private theorem lowerTwo_row_260 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 260 j) = 0 := by decide
private theorem lowerTwo_row_261 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 261 j) = 0 := by decide
private theorem lowerTwo_row_262 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 262 j) = 0 := by decide
private theorem lowerTwo_row_263 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 263 j) = 0 := by decide
private theorem lowerTwo_row_264 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 264 j) = 0 := by decide
private theorem lowerTwo_row_265 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 265 j) = 0 := by decide
private theorem lowerTwo_row_266 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 266 j) = 0 := by decide
private theorem lowerTwo_row_267 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 267 j) = 0 := by decide
private theorem lowerTwo_row_268 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 268 j) = 0 := by decide
private theorem lowerTwo_row_269 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 269 j) = 0 := by decide
private theorem lowerTwo_row_270 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 270 j) = 0 := by decide
private theorem lowerTwo_row_271 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 271 j) = 0 := by decide
private theorem lowerTwo_row_272 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 272 j) = 0 := by decide
private theorem lowerTwo_row_273 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 273 j) = 0 := by decide
private theorem lowerTwo_row_274 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 274 j) = 0 := by decide
private theorem lowerTwo_row_275 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 275 j) = 0 := by decide
private theorem lowerTwo_row_276 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 276 j) = 0 := by decide
private theorem lowerTwo_row_277 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 277 j) = 0 := by decide
private theorem lowerTwo_row_278 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 278 j) = 0 := by decide
private theorem lowerTwo_row_279 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 279 j) = 0 := by decide
private theorem lowerTwo_row_280 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 280 j) = 0 := by decide
private theorem lowerTwo_row_281 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 281 j) = 0 := by decide
private theorem lowerTwo_row_282 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 282 j) = 0 := by decide
private theorem lowerTwo_row_283 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 283 j) = 0 := by decide
private theorem lowerTwo_row_284 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 284 j) = 0 := by decide
private theorem lowerTwo_row_285 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 285 j) = 0 := by decide
private theorem lowerTwo_row_286 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 286 j) = 0 := by decide
private theorem lowerTwo_row_287 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 287 j) = 0 := by decide
private theorem lowerTwo_row_288 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 288 j) = 0 := by decide
private theorem lowerTwo_row_289 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 289 j) = 0 := by decide
private theorem lowerTwo_row_290 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 290 j) = 0 := by decide
private theorem lowerTwo_row_291 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 291 j) = 0 := by decide
private theorem lowerTwo_row_292 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 292 j) = 0 := by decide
private theorem lowerTwo_row_293 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 293 j) = 0 := by decide
private theorem lowerTwo_row_294 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 294 j) = 0 := by decide
private theorem lowerTwo_row_295 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 295 j) = 0 := by decide
private theorem lowerTwo_row_296 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 296 j) = 0 := by decide
private theorem lowerTwo_row_297 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 297 j) = 0 := by decide
private theorem lowerTwo_row_298 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 298 j) = 0 := by decide
private theorem lowerTwo_row_299 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 299 j) = 0 := by decide
private theorem lowerTwo_row_300 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 300 j) = 0 := by decide
private theorem lowerTwo_row_301 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 301 j) = 0 := by decide
private theorem lowerTwo_row_302 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 302 j) = 0 := by decide
private theorem lowerTwo_row_303 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 303 j) = 0 := by decide
private theorem lowerTwo_row_304 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 304 j) = 0 := by decide
private theorem lowerTwo_row_305 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 305 j) = 0 := by decide
private theorem lowerTwo_row_306 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 306 j) = 0 := by decide
private theorem lowerTwo_row_307 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 307 j) = 0 := by decide
private theorem lowerTwo_row_308 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 308 j) = 0 := by decide
private theorem lowerTwo_row_309 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 309 j) = 0 := by decide
private theorem lowerTwo_row_310 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 310 j) = 0 := by decide
private theorem lowerTwo_row_311 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 311 j) = 0 := by decide
private theorem lowerTwo_row_312 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 312 j) = 0 := by decide
private theorem lowerTwo_row_313 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 313 j) = 0 := by decide
private theorem lowerTwo_row_314 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 314 j) = 0 := by decide
private theorem lowerTwo_row_315 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 315 j) = 0 := by decide
private theorem lowerTwo_row_316 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 316 j) = 0 := by decide
private theorem lowerTwo_row_317 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 317 j) = 0 := by decide
private theorem lowerTwo_row_318 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 318 j) = 0 := by decide
private theorem lowerTwo_row_319 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 319 j) = 0 := by decide
private theorem lowerTwo_row_320 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 320 j) = 0 := by decide
private theorem lowerTwo_row_321 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 321 j) = 0 := by decide
private theorem lowerTwo_row_322 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 322 j) = 0 := by decide
private theorem lowerTwo_row_323 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 323 j) = 0 := by decide
private theorem lowerTwo_row_324 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 324 j) = 0 := by decide
private theorem lowerTwo_row_325 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 325 j) = 0 := by decide
private theorem lowerTwo_row_326 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 326 j) = 0 := by decide
private theorem lowerTwo_row_327 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 327 j) = 0 := by decide
private theorem lowerTwo_row_328 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 328 j) = 0 := by decide
private theorem lowerTwo_row_329 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 329 j) = 0 := by decide
private theorem lowerTwo_row_330 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 330 j) = 0 := by decide
private theorem lowerTwo_row_331 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 331 j) = 0 := by decide
private theorem lowerTwo_row_332 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 332 j) = 0 := by decide
private theorem lowerTwo_row_333 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 333 j) = 0 := by decide
private theorem lowerTwo_row_334 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 334 j) = 0 := by decide
private theorem lowerTwo_row_335 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 335 j) = 0 := by decide
private theorem lowerTwo_row_336 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 336 j) = 0 := by decide
private theorem lowerTwo_row_337 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 337 j) = 0 := by decide
private theorem lowerTwo_row_338 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 338 j) = 0 := by decide
private theorem lowerTwo_row_339 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 339 j) = 0 := by decide
private theorem lowerTwo_row_340 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 340 j) = 0 := by decide
private theorem lowerTwo_row_341 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 341 j) = 0 := by decide
private theorem lowerTwo_row_342 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 342 j) = 0 := by decide
private theorem lowerTwo_row_343 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 343 j) = 0 := by decide
private theorem lowerTwo_row_344 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 344 j) = 0 := by decide
private theorem lowerTwo_row_345 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 345 j) = 0 := by decide
private theorem lowerTwo_row_346 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 346 j) = 0 := by decide
private theorem lowerTwo_row_347 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 347 j) = 0 := by decide
private theorem lowerTwo_row_348 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 348 j) = 0 := by decide
private theorem lowerTwo_row_349 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 349 j) = 0 := by decide
private theorem lowerTwo_row_350 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 350 j) = 0 := by decide
private theorem lowerTwo_row_351 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 351 j) = 0 := by decide
private theorem lowerTwo_row_352 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 352 j) = 0 := by decide
private theorem lowerTwo_row_353 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 353 j) = 0 := by decide
private theorem lowerTwo_row_354 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 354 j) = 0 := by decide
private theorem lowerTwo_row_355 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 355 j) = 0 := by decide
private theorem lowerTwo_row_356 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 356 j) = 0 := by decide
private theorem lowerTwo_row_357 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 357 j) = 0 := by decide
private theorem lowerTwo_row_358 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 358 j) = 0 := by decide
private theorem lowerTwo_row_359 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 359 j) = 0 := by decide
private theorem lowerTwo_row_360 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 360 j) = 0 := by decide
private theorem lowerTwo_row_361 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 361 j) = 0 := by decide
private theorem lowerTwo_row_362 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 362 j) = 0 := by decide
private theorem lowerTwo_row_363 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 363 j) = 0 := by decide
private theorem lowerTwo_row_364 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 364 j) = 0 := by decide
private theorem lowerTwo_row_365 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 365 j) = 0 := by decide
private theorem lowerTwo_row_366 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 366 j) = 0 := by decide
private theorem lowerTwo_row_367 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 367 j) = 0 := by decide
private theorem lowerTwo_row_368 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 368 j) = 0 := by decide
private theorem lowerTwo_row_369 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 369 j) = 0 := by decide
private theorem lowerTwo_row_370 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 370 j) = 0 := by decide
private theorem lowerTwo_row_371 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 371 j) = 0 := by decide
private theorem lowerTwo_row_372 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 372 j) = 0 := by decide
private theorem lowerTwo_row_373 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 373 j) = 0 := by decide
private theorem lowerTwo_row_374 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 374 j) = 0 := by decide
private theorem lowerTwo_row_375 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 375 j) = 0 := by decide
private theorem lowerTwo_row_376 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 376 j) = 0 := by decide
private theorem lowerTwo_row_377 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 377 j) = 0 := by decide
private theorem lowerTwo_row_378 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 378 j) = 0 := by decide
private theorem lowerTwo_row_379 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 379 j) = 0 := by decide
private theorem lowerTwo_row_380 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 380 j) = 0 := by decide
private theorem lowerTwo_row_381 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 381 j) = 0 := by decide
private theorem lowerTwo_row_382 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 382 j) = 0 := by decide
private theorem lowerTwo_row_383 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 383 j) = 0 := by decide
private theorem lowerTwo_row_384 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 384 j) = 0 := by decide
private theorem lowerTwo_row_385 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 385 j) = 0 := by decide
private theorem lowerTwo_row_386 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 386 j) = 0 := by decide
private theorem lowerTwo_row_387 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 387 j) = 0 := by decide
private theorem lowerTwo_row_388 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 388 j) = 0 := by decide
private theorem lowerTwo_row_389 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 389 j) = 0 := by decide
private theorem lowerTwo_row_390 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 390 j) = 0 := by decide
private theorem lowerTwo_row_391 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 391 j) = 0 := by decide
private theorem lowerTwo_row_392 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 392 j) = 0 := by decide
private theorem lowerTwo_row_393 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 393 j) = 0 := by decide
private theorem lowerTwo_row_394 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 394 j) = 0 := by decide
private theorem lowerTwo_row_395 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 395 j) = 0 := by decide
private theorem lowerTwo_row_396 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 396 j) = 0 := by decide
private theorem lowerTwo_row_397 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 397 j) = 0 := by decide
private theorem lowerTwo_row_398 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 398 j) = 0 := by decide
private theorem lowerTwo_row_399 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 399 j) = 0 := by decide
private theorem lowerTwo_row_400 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 400 j) = 0 := by decide
private theorem lowerTwo_row_401 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 401 j) = 0 := by decide
private theorem lowerTwo_row_402 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 402 j) = 0 := by decide
private theorem lowerTwo_row_403 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 403 j) = 0 := by decide
private theorem lowerTwo_row_404 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 404 j) = 0 := by decide
private theorem lowerTwo_row_405 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 405 j) = 0 := by decide
private theorem lowerTwo_row_406 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 406 j) = 0 := by decide
private theorem lowerTwo_row_407 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 407 j) = 0 := by decide
private theorem lowerTwo_row_408 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 408 j) = 0 := by decide
private theorem lowerTwo_row_409 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 409 j) = 0 := by decide
private theorem lowerTwo_row_410 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 410 j) = 0 := by decide
private theorem lowerTwo_row_411 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 411 j) = 0 := by decide
private theorem lowerTwo_row_412 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 412 j) = 0 := by decide
private theorem lowerTwo_row_413 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 413 j) = 0 := by decide
private theorem lowerTwo_row_414 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 414 j) = 0 := by decide
private theorem lowerTwo_row_415 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 415 j) = 0 := by decide
private theorem lowerTwo_row_416 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 416 j) = 0 := by decide
private theorem lowerTwo_row_417 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 417 j) = 0 := by decide
private theorem lowerTwo_row_418 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 418 j) = 0 := by decide
private theorem lowerTwo_row_419 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 419 j) = 0 := by decide
private theorem lowerTwo_row_420 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 420 j) = 0 := by decide
private theorem lowerTwo_row_421 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 421 j) = 0 := by decide
private theorem lowerTwo_row_422 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 422 j) = 0 := by decide
private theorem lowerTwo_row_423 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 423 j) = 0 := by decide
private theorem lowerTwo_row_424 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 424 j) = 0 := by decide
private theorem lowerTwo_row_425 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 425 j) = 0 := by decide
private theorem lowerTwo_row_426 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 426 j) = 0 := by decide
private theorem lowerTwo_row_427 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 427 j) = 0 := by decide
private theorem lowerTwo_row_428 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 428 j) = 0 := by decide
private theorem lowerTwo_row_429 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 429 j) = 0 := by decide
private theorem lowerTwo_row_430 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 430 j) = 0 := by decide
private theorem lowerTwo_row_431 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 431 j) = 0 := by decide
private theorem lowerTwo_row_432 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 432 j) = 0 := by decide
private theorem lowerTwo_row_433 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 433 j) = 0 := by decide
private theorem lowerTwo_row_434 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 434 j) = 0 := by decide
private theorem lowerTwo_row_435 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 435 j) = 0 := by decide
private theorem lowerTwo_row_436 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 436 j) = 0 := by decide
private theorem lowerTwo_row_437 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 437 j) = 0 := by decide
private theorem lowerTwo_row_438 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 438 j) = 0 := by decide
private theorem lowerTwo_row_439 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 439 j) = 0 := by decide
private theorem lowerTwo_row_440 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 440 j) = 0 := by decide
private theorem lowerTwo_row_441 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 441 j) = 0 := by decide
private theorem lowerTwo_row_442 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 442 j) = 0 := by decide
private theorem lowerTwo_row_443 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 443 j) = 0 := by decide
private theorem lowerTwo_row_444 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 444 j) = 0 := by decide
private theorem lowerTwo_row_445 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 445 j) = 0 := by decide
private theorem lowerTwo_row_446 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 446 j) = 0 := by decide
private theorem lowerTwo_row_447 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 447 j) = 0 := by decide
private theorem lowerTwo_row_448 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 448 j) = 0 := by decide
private theorem lowerTwo_row_449 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 449 j) = 0 := by decide
private theorem lowerTwo_row_450 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 450 j) = 0 := by decide
private theorem lowerTwo_row_451 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 451 j) = 0 := by decide
private theorem lowerTwo_row_452 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 452 j) = 0 := by decide
private theorem lowerTwo_row_453 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 453 j) = 0 := by decide
private theorem lowerTwo_row_454 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 454 j) = 0 := by decide
private theorem lowerTwo_row_455 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 455 j) = 0 := by decide
private theorem lowerTwo_row_456 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 456 j) = 0 := by decide
private theorem lowerTwo_row_457 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 457 j) = 0 := by decide
private theorem lowerTwo_row_458 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 458 j) = 0 := by decide
private theorem lowerTwo_row_459 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 459 j) = 0 := by decide
private theorem lowerTwo_row_460 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 460 j) = 0 := by decide
private theorem lowerTwo_row_461 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 461 j) = 0 := by decide
private theorem lowerTwo_row_462 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 462 j) = 0 := by decide
private theorem lowerTwo_row_463 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 463 j) = 0 := by decide
private theorem lowerTwo_row_464 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 464 j) = 0 := by decide
private theorem lowerTwo_row_465 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 465 j) = 0 := by decide
private theorem lowerTwo_row_466 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 466 j) = 0 := by decide
private theorem lowerTwo_row_467 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 467 j) = 0 := by decide
private theorem lowerTwo_row_468 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 468 j) = 0 := by decide
private theorem lowerTwo_row_469 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 469 j) = 0 := by decide
private theorem lowerTwo_row_470 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 470 j) = 0 := by decide
private theorem lowerTwo_row_471 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 471 j) = 0 := by decide
private theorem lowerTwo_row_472 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 472 j) = 0 := by decide
private theorem lowerTwo_row_473 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 473 j) = 0 := by decide
private theorem lowerTwo_row_474 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 474 j) = 0 := by decide
private theorem lowerTwo_row_475 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 475 j) = 0 := by decide
private theorem lowerTwo_row_476 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 476 j) = 0 := by decide
private theorem lowerTwo_row_477 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 477 j) = 0 := by decide
private theorem lowerTwo_row_478 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 478 j) = 0 := by decide
private theorem lowerTwo_row_479 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 479 j) = 0 := by decide
private theorem lowerTwo_row_480 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 480 j) = 0 := by decide
private theorem lowerTwo_row_481 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 481 j) = 0 := by decide
private theorem lowerTwo_row_482 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 482 j) = 0 := by decide
private theorem lowerTwo_row_483 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 483 j) = 0 := by decide
private theorem lowerTwo_row_484 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 484 j) = 0 := by decide
private theorem lowerTwo_row_485 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 485 j) = 0 := by decide
private theorem lowerTwo_row_486 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 486 j) = 0 := by decide
private theorem lowerTwo_row_487 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 487 j) = 0 := by decide
private theorem lowerTwo_row_488 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 488 j) = 0 := by decide
private theorem lowerTwo_row_489 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 489 j) = 0 := by decide
private theorem lowerTwo_row_490 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 490 j) = 0 := by decide
private theorem lowerTwo_row_491 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 491 j) = 0 := by decide
private theorem lowerTwo_row_492 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 492 j) = 0 := by decide
private theorem lowerTwo_row_493 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 493 j) = 0 := by decide
private theorem lowerTwo_row_494 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 494 j) = 0 := by decide
private theorem lowerTwo_row_495 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 495 j) = 0 := by decide
private theorem lowerTwo_row_496 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 496 j) = 0 := by decide
private theorem lowerTwo_row_497 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 497 j) = 0 := by decide
private theorem lowerTwo_row_498 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 498 j) = 0 := by decide
private theorem lowerTwo_row_499 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 499 j) = 0 := by decide
private theorem lowerTwo_row_500 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 500 j) = 0 := by decide
private theorem lowerTwo_row_501 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 501 j) = 0 := by decide
private theorem lowerTwo_row_502 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 502 j) = 0 := by decide
private theorem lowerTwo_row_503 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 503 j) = 0 := by decide
private theorem lowerTwo_row_504 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 504 j) = 0 := by decide
private theorem lowerTwo_row_505 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 505 j) = 0 := by decide
private theorem lowerTwo_row_506 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 506 j) = 0 := by decide
private theorem lowerTwo_row_507 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 507 j) = 0 := by decide
private theorem lowerTwo_row_508 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 508 j) = 0 := by decide
private theorem lowerTwo_row_509 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 509 j) = 0 := by decide
private theorem lowerTwo_row_510 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 510 j) = 0 := by decide
private theorem lowerTwo_row_511 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 511 j) = 0 := by decide
private theorem lowerTwo_row_512 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 512 j) = 0 := by decide
private theorem lowerTwo_row_513 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 513 j) = 0 := by decide
private theorem lowerTwo_row_514 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 514 j) = 0 := by decide
private theorem lowerTwo_row_515 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 515 j) = 0 := by decide
private theorem lowerTwo_row_516 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 516 j) = 0 := by decide
private theorem lowerTwo_row_517 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 517 j) = 0 := by decide
private theorem lowerTwo_row_518 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 518 j) = 0 := by decide
private theorem lowerTwo_row_519 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 519 j) = 0 := by decide
private theorem lowerTwo_row_520 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 520 j) = 0 := by decide
private theorem lowerTwo_row_521 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 521 j) = 0 := by decide
private theorem lowerTwo_row_522 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 522 j) = 0 := by decide
private theorem lowerTwo_row_523 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 523 j) = 0 := by decide
private theorem lowerTwo_row_524 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 524 j) = 0 := by decide
private theorem lowerTwo_row_525 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 525 j) = 0 := by decide
private theorem lowerTwo_row_526 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 526 j) = 0 := by decide
private theorem lowerTwo_row_527 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 527 j) = 0 := by decide
private theorem lowerTwo_row_528 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 528 j) = 0 := by decide
private theorem lowerTwo_row_529 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 529 j) = 0 := by decide
private theorem lowerTwo_row_530 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 530 j) = 0 := by decide
private theorem lowerTwo_row_531 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 531 j) = 0 := by decide
private theorem lowerTwo_row_532 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 532 j) = 0 := by decide
private theorem lowerTwo_row_533 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 533 j) = 0 := by decide
private theorem lowerTwo_row_534 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 534 j) = 0 := by decide
private theorem lowerTwo_row_535 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 535 j) = 0 := by decide
private theorem lowerTwo_row_536 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 536 j) = 0 := by decide
private theorem lowerTwo_row_537 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 537 j) = 0 := by decide
private theorem lowerTwo_row_538 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 538 j) = 0 := by decide
private theorem lowerTwo_row_539 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 539 j) = 0 := by decide
private theorem lowerTwo_row_540 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 540 j) = 0 := by decide
private theorem lowerTwo_row_541 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 541 j) = 0 := by decide
private theorem lowerTwo_row_542 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 542 j) = 0 := by decide
private theorem lowerTwo_row_543 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 543 j) = 0 := by decide
private theorem lowerTwo_row_544 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 544 j) = 0 := by decide
private theorem lowerTwo_row_545 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 545 j) = 0 := by decide
private theorem lowerTwo_row_546 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 546 j) = 0 := by decide
private theorem lowerTwo_row_547 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 547 j) = 0 := by decide
private theorem lowerTwo_row_548 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 548 j) = 0 := by decide
private theorem lowerTwo_row_549 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 549 j) = 0 := by decide
private theorem lowerTwo_row_550 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 550 j) = 0 := by decide
private theorem lowerTwo_row_551 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 551 j) = 0 := by decide
private theorem lowerTwo_row_552 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 552 j) = 0 := by decide
private theorem lowerTwo_row_553 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 553 j) = 0 := by decide
private theorem lowerTwo_row_554 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 554 j) = 0 := by decide
private theorem lowerTwo_row_555 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 555 j) = 0 := by decide
private theorem lowerTwo_row_556 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 556 j) = 0 := by decide
private theorem lowerTwo_row_557 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 557 j) = 0 := by decide
private theorem lowerTwo_row_558 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 558 j) = 0 := by decide
private theorem lowerTwo_row_559 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 559 j) = 0 := by decide
private theorem lowerTwo_row_560 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 560 j) = 0 := by decide
private theorem lowerTwo_row_561 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 561 j) = 0 := by decide
private theorem lowerTwo_row_562 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 562 j) = 0 := by decide
private theorem lowerTwo_row_563 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 563 j) = 0 := by decide
private theorem lowerTwo_row_564 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 564 j) = 0 := by decide
private theorem lowerTwo_row_565 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 565 j) = 0 := by decide
private theorem lowerTwo_row_566 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 566 j) = 0 := by decide
private theorem lowerTwo_row_567 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 567 j) = 0 := by decide
private theorem lowerTwo_row_568 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 568 j) = 0 := by decide
private theorem lowerTwo_row_569 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 569 j) = 0 := by decide
private theorem lowerTwo_row_570 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 570 j) = 0 := by decide
private theorem lowerTwo_row_571 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 571 j) = 0 := by decide
private theorem lowerTwo_row_572 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 572 j) = 0 := by decide
private theorem lowerTwo_row_573 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 573 j) = 0 := by decide
private theorem lowerTwo_row_574 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 574 j) = 0 := by decide
private theorem lowerTwo_row_575 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 575 j) = 0 := by decide
private theorem lowerTwo_row_576 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 576 j) = 0 := by decide
private theorem lowerTwo_row_577 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 577 j) = 0 := by decide
private theorem lowerTwo_row_578 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 578 j) = 0 := by decide
private theorem lowerTwo_row_579 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 579 j) = 0 := by decide
private theorem lowerTwo_row_580 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 580 j) = 0 := by decide
private theorem lowerTwo_row_581 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 581 j) = 0 := by decide
private theorem lowerTwo_row_582 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 582 j) = 0 := by decide
private theorem lowerTwo_row_583 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 583 j) = 0 := by decide
private theorem lowerTwo_row_584 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 584 j) = 0 := by decide
private theorem lowerTwo_row_585 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 585 j) = 0 := by decide
private theorem lowerTwo_row_586 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 586 j) = 0 := by decide
private theorem lowerTwo_row_587 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 587 j) = 0 := by decide
private theorem lowerTwo_row_588 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 588 j) = 0 := by decide
private theorem lowerTwo_row_589 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 589 j) = 0 := by decide
private theorem lowerTwo_row_590 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 590 j) = 0 := by decide
private theorem lowerTwo_row_591 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 591 j) = 0 := by decide
private theorem lowerTwo_row_592 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 592 j) = 0 := by decide
private theorem lowerTwo_row_593 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 593 j) = 0 := by decide
private theorem lowerTwo_row_594 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 594 j) = 0 := by decide
private theorem lowerTwo_row_595 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 595 j) = 0 := by decide
private theorem lowerTwo_row_596 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 596 j) = 0 := by decide
private theorem lowerTwo_row_597 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 597 j) = 0 := by decide
private theorem lowerTwo_row_598 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 598 j) = 0 := by decide
private theorem lowerTwo_row_599 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 599 j) = 0 := by decide
private theorem lowerTwo_row_600 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 600 j) = 0 := by decide
private theorem lowerTwo_row_601 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 601 j) = 0 := by decide
private theorem lowerTwo_row_602 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 602 j) = 0 := by decide
private theorem lowerTwo_row_603 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 603 j) = 0 := by decide
private theorem lowerTwo_row_604 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 604 j) = 0 := by decide
private theorem lowerTwo_row_605 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 605 j) = 0 := by decide
private theorem lowerTwo_row_606 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 606 j) = 0 := by decide
private theorem lowerTwo_row_607 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 607 j) = 0 := by decide
private theorem lowerTwo_row_608 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 608 j) = 0 := by decide
private theorem lowerTwo_row_609 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 609 j) = 0 := by decide
private theorem lowerTwo_row_610 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 610 j) = 0 := by decide
private theorem lowerTwo_row_611 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 611 j) = 0 := by decide
private theorem lowerTwo_row_612 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 612 j) = 0 := by decide
private theorem lowerTwo_row_613 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 613 j) = 0 := by decide
private theorem lowerTwo_row_614 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 614 j) = 0 := by decide
private theorem lowerTwo_row_615 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 615 j) = 0 := by decide
private theorem lowerTwo_row_616 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 616 j) = 0 := by decide
private theorem lowerTwo_row_617 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 617 j) = 0 := by decide
private theorem lowerTwo_row_618 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 618 j) = 0 := by decide
private theorem lowerTwo_row_619 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 619 j) = 0 := by decide
private theorem lowerTwo_row_620 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 620 j) = 0 := by decide
private theorem lowerTwo_row_621 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 621 j) = 0 := by decide
private theorem lowerTwo_row_622 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 622 j) = 0 := by decide
private theorem lowerTwo_row_623 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 623 j) = 0 := by decide
private theorem lowerTwo_row_624 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 624 j) = 0 := by decide
private theorem lowerTwo_row_625 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 625 j) = 0 := by decide
private theorem lowerTwo_row_626 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 626 j) = 0 := by decide
private theorem lowerTwo_row_627 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 627 j) = 0 := by decide
private theorem lowerTwo_row_628 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 628 j) = 0 := by decide
private theorem lowerTwo_row_629 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 629 j) = 0 := by decide
private theorem lowerTwo_row_630 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 630 j) = 0 := by decide
private theorem lowerTwo_row_631 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 631 j) = 0 := by decide
private theorem lowerTwo_row_632 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 632 j) = 0 := by decide
private theorem lowerTwo_row_633 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 633 j) = 0 := by decide
private theorem lowerTwo_row_634 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 634 j) = 0 := by decide
private theorem lowerTwo_row_635 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 635 j) = 0 := by decide
private theorem lowerTwo_row_636 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 636 j) = 0 := by decide
private theorem lowerTwo_row_637 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 637 j) = 0 := by decide
private theorem lowerTwo_row_638 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 638 j) = 0 := by decide
private theorem lowerTwo_row_639 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 639 j) = 0 := by decide
private theorem lowerTwo_row_640 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 640 j) = 0 := by decide
private theorem lowerTwo_row_641 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 641 j) = 0 := by decide
private theorem lowerTwo_row_642 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 642 j) = 0 := by decide
private theorem lowerTwo_row_643 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 643 j) = 0 := by decide
private theorem lowerTwo_row_644 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 644 j) = 0 := by decide
private theorem lowerTwo_row_645 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 645 j) = 0 := by decide
private theorem lowerTwo_row_646 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 646 j) = 0 := by decide
private theorem lowerTwo_row_647 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 647 j) = 0 := by decide
private theorem lowerTwo_row_648 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 648 j) = 0 := by decide
private theorem lowerTwo_row_649 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 649 j) = 0 := by decide
private theorem lowerTwo_row_650 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 650 j) = 0 := by decide
private theorem lowerTwo_row_651 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 651 j) = 0 := by decide
private theorem lowerTwo_row_652 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 652 j) = 0 := by decide
private theorem lowerTwo_row_653 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 653 j) = 0 := by decide
private theorem lowerTwo_row_654 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 654 j) = 0 := by decide
private theorem lowerTwo_row_655 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 655 j) = 0 := by decide
private theorem lowerTwo_row_656 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 656 j) = 0 := by decide
private theorem lowerTwo_row_657 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 657 j) = 0 := by decide
private theorem lowerTwo_row_658 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 658 j) = 0 := by decide
private theorem lowerTwo_row_659 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 659 j) = 0 := by decide
private theorem lowerTwo_row_660 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 660 j) = 0 := by decide
private theorem lowerTwo_row_661 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 661 j) = 0 := by decide
private theorem lowerTwo_row_662 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 662 j) = 0 := by decide
private theorem lowerTwo_row_663 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 663 j) = 0 := by decide
private theorem lowerTwo_row_664 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 664 j) = 0 := by decide
private theorem lowerTwo_row_665 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 665 j) = 0 := by decide
private theorem lowerTwo_row_666 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 666 j) = 0 := by decide
private theorem lowerTwo_row_667 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 667 j) = 0 := by decide
private theorem lowerTwo_row_668 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 668 j) = 0 := by decide
private theorem lowerTwo_row_669 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 669 j) = 0 := by decide
private theorem lowerTwo_row_670 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 670 j) = 0 := by decide
private theorem lowerTwo_row_671 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 671 j) = 0 := by decide
private theorem lowerTwo_row_672 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 672 j) = 0 := by decide
private theorem lowerTwo_row_673 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 673 j) = 0 := by decide
private theorem lowerTwo_row_674 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 674 j) = 0 := by decide
private theorem lowerTwo_row_675 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 675 j) = 0 := by decide
private theorem lowerTwo_row_676 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 676 j) = 0 := by decide
private theorem lowerTwo_row_677 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 677 j) = 0 := by decide
private theorem lowerTwo_row_678 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 678 j) = 0 := by decide
private theorem lowerTwo_row_679 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 679 j) = 0 := by decide
private theorem lowerTwo_row_680 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 680 j) = 0 := by decide
private theorem lowerTwo_row_681 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 681 j) = 0 := by decide
private theorem lowerTwo_row_682 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 682 j) = 1721829 := by decide
private theorem lowerTwo_row_683 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 683 j) = 860914 := by decide
private theorem lowerTwo_row_684 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 684 j) = 861335 := by decide
private theorem lowerTwo_row_685 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 685 j) = 0 := by decide
private theorem lowerTwo_row_686 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 686 j) = 0 := by decide
private theorem lowerTwo_row_687 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 687 j) = 0 := by decide
private theorem lowerTwo_row_688 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 688 j) = 0 := by decide
private theorem lowerTwo_row_689 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 689 j) = 0 := by decide
private theorem lowerTwo_row_690 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 690 j) = 0 := by decide
private theorem lowerTwo_row_691 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 691 j) = 0 := by decide
private theorem lowerTwo_row_692 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 692 j) = 0 := by decide
private theorem lowerTwo_row_693 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 693 j) = 0 := by decide
private theorem lowerTwo_row_694 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 694 j) = 0 := by decide
private theorem lowerTwo_row_695 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 695 j) = 0 := by decide
private theorem lowerTwo_row_696 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 696 j) = 0 := by decide
private theorem lowerTwo_row_697 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 697 j) = 0 := by decide
private theorem lowerTwo_row_698 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 698 j) = 0 := by decide
private theorem lowerTwo_row_699 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 699 j) = 0 := by decide
private theorem lowerTwo_row_700 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 700 j) = 0 := by decide
private theorem lowerTwo_row_701 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 701 j) = 0 := by decide
private theorem lowerTwo_row_702 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 702 j) = 0 := by decide
private theorem lowerTwo_row_703 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 703 j) = 0 := by decide
private theorem lowerTwo_row_704 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 704 j) = 0 := by decide
private theorem lowerTwo_row_705 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 705 j) = 0 := by decide
private theorem lowerTwo_row_706 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 706 j) = 0 := by decide
private theorem lowerTwo_row_707 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 707 j) = 0 := by decide
private theorem lowerTwo_row_708 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 708 j) = 0 := by decide
private theorem lowerTwo_row_709 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 709 j) = 0 := by decide
private theorem lowerTwo_row_710 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 710 j) = 0 := by decide
private theorem lowerTwo_row_711 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 711 j) = 0 := by decide
private theorem lowerTwo_row_712 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 712 j) = 0 := by decide
private theorem lowerTwo_row_713 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 713 j) = 0 := by decide
private theorem lowerTwo_row_714 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 714 j) = 0 := by decide
private theorem lowerTwo_row_715 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 715 j) = 0 := by decide
private theorem lowerTwo_row_716 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 716 j) = 0 := by decide
private theorem lowerTwo_row_717 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 717 j) = 0 := by decide
private theorem lowerTwo_row_718 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 718 j) = 0 := by decide
private theorem lowerTwo_row_719 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 719 j) = 0 := by decide
private theorem lowerTwo_row_720 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 720 j) = 0 := by decide
private theorem lowerTwo_row_721 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 721 j) = 0 := by decide
private theorem lowerTwo_row_722 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 722 j) = 0 := by decide
private theorem lowerTwo_row_723 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 723 j) = 0 := by decide
private theorem lowerTwo_row_724 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 724 j) = 0 := by decide
private theorem lowerTwo_row_725 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 725 j) = 0 := by decide
private theorem lowerTwo_row_726 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 726 j) = 0 := by decide
private theorem lowerTwo_row_727 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 727 j) = 0 := by decide
private theorem lowerTwo_row_728 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 728 j) = 0 := by decide
private theorem lowerTwo_row_729 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 729 j) = 0 := by decide
private theorem lowerTwo_row_730 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 730 j) = 0 := by decide
private theorem lowerTwo_row_731 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 731 j) = 0 := by decide
private theorem lowerTwo_row_732 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 732 j) = 0 := by decide
private theorem lowerTwo_row_733 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 733 j) = 0 := by decide
private theorem lowerTwo_row_734 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 734 j) = 0 := by decide
private theorem lowerTwo_row_735 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 735 j) = 0 := by decide
private theorem lowerTwo_row_736 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 736 j) = 0 := by decide
private theorem lowerTwo_row_737 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 737 j) = 0 := by decide
private theorem lowerTwo_row_738 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 738 j) = 0 := by decide
private theorem lowerTwo_row_739 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 739 j) = 0 := by decide
private theorem lowerTwo_row_740 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 740 j) = 0 := by decide
private theorem lowerTwo_row_741 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 741 j) = 0 := by decide
private theorem lowerTwo_row_742 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 742 j) = 0 := by decide
private theorem lowerTwo_row_743 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 743 j) = 0 := by decide
private theorem lowerTwo_row_744 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 744 j) = 1574430 := by decide
private theorem lowerTwo_row_745 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 745 j) = 2359408 := by decide
private theorem lowerTwo_row_746 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 746 j) = 3930489 := by decide
private theorem lowerTwo_row_747 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 747 j) = 5500085 := by decide
private theorem lowerTwo_row_748 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 748 j) = 6279866 := by decide
private theorem lowerTwo_row_749 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 749 j) = 7846137 := by decide
private theorem lowerTwo_row_750 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 750 j) = 8622594 := by decide
private theorem lowerTwo_row_751 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 751 j) = 10185549 := by decide
private theorem lowerTwo_row_752 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 752 j) = 10958697 := by decide
private theorem lowerTwo_row_753 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 753 j) = 12518357 := by decide
private theorem lowerTwo_row_754 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 754 j) = 14076557 := by decide
private theorem lowerTwo_row_755 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 755 j) = 14844581 := by decide
private theorem lowerTwo_row_756 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 756 j) = 16399510 := by decide
private theorem lowerTwo_row_757 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 757 j) = 17164253 := by decide
private theorem lowerTwo_row_758 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 758 j) = 18715918 := by decide
private theorem lowerTwo_row_759 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 759 j) = 19477406 := by decide
private theorem lowerTwo_row_760 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 760 j) = 21025818 := by decide
private theorem lowerTwo_row_761 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 761 j) = 22572808 := by decide
private theorem lowerTwo_row_762 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 762 j) = 23329240 := by decide
private theorem lowerTwo_row_763 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 763 j) = 24873003 := by decide
private theorem lowerTwo_row_764 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 764 j) = 25626200 := by decide
private theorem lowerTwo_row_765 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 765 j) = 27166752 := by decide
private theorem lowerTwo_row_766 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 766 j) = 27916743 := by decide
private theorem lowerTwo_row_767 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 767 j) = 29454091 := by decide
private theorem lowerTwo_row_768 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 768 j) = 30990042 := by decide
private theorem lowerTwo_row_769 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 769 j) = 31735043 := by decide
private theorem lowerTwo_row_770 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 770 j) = 33267820 := by decide
private theorem lowerTwo_row_771 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 771 j) = 34009641 := by decide
private theorem lowerTwo_row_772 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 772 j) = 35539249 := by decide
private theorem lowerTwo_row_773 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 773 j) = 36277896 := by decide
private theorem lowerTwo_row_774 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 774 j) = 37804363 := by decide
private theorem lowerTwo_row_775 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 775 j) = 39329452 := by decide
private theorem lowerTwo_row_776 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 776 j) = 40063185 := by decide
private theorem lowerTwo_row_777 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 777 j) = 41585145 := by decide
private theorem lowerTwo_row_778 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 778 j) = 42315735 := by decide
private theorem lowerTwo_row_779 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 779 j) = 43834586 := by decide
private theorem lowerTwo_row_780 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 780 j) = 44562056 := by decide
private theorem lowerTwo_row_781 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 781 j) = 46077809 := by decide
private theorem lowerTwo_row_782 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 782 j) = 47592205 := by decide
private theorem lowerTwo_row_783 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 783 j) = 48314820 := by decide
private theorem lowerTwo_row_784 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 784 j) = 49826147 := by decide
private theorem lowerTwo_row_785 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 785 j) = 50545666 := by decide
private theorem lowerTwo_row_786 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 786 j) = 52053930 := by decide
private theorem lowerTwo_row_787 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 787 j) = 52770358 := by decide
private theorem lowerTwo_row_788 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 788 j) = 54275573 := by decide
private theorem lowerTwo_row_789 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 789 j) = 55779448 := by decide
private theorem lowerTwo_row_790 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 790 j) = 56491111 := by decide
private theorem lowerTwo_row_791 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 791 j) = 57991961 := by decide
private theorem lowerTwo_row_792 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 792 j) = 58700568 := by decide
private theorem lowerTwo_row_793 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 793 j) = 60198394 := by decide
private theorem lowerTwo_row_794 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 794 j) = 60903971 := by decide
private theorem lowerTwo_row_795 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 795 j) = 62398798 := by decide
private theorem lowerTwo_row_796 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 796 j) = 63892321 := by decide
private theorem lowerTwo_row_797 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 797 j) = 64593176 := by decide
private theorem lowerTwo_row_798 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 798 j) = 66083712 := by decide
private theorem lowerTwo_row_799 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 799 j) = 66781555 := by decide
private theorem lowerTwo_row_800 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 800 j) = 68269128 := by decide
private theorem lowerTwo_row_801 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 801 j) = 68963978 := by decide
private theorem lowerTwo_row_802 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 802 j) = 70448588 := by decide
private theorem lowerTwo_row_803 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 803 j) = 71931925 := by decide
private theorem lowerTwo_row_804 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 804 j) = 72622121 := by decide
private theorem lowerTwo_row_805 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 805 j) = 74102517 := by decide
private theorem lowerTwo_row_806 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 806 j) = 74789745 := by decide
private theorem lowerTwo_row_807 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 807 j) = 76267215 := by decide
private theorem lowerTwo_row_808 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 808 j) = 76951492 := by decide
private theorem lowerTwo_row_809 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 809 j) = 78426055 := by decide
private theorem lowerTwo_row_810 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 810 j) = 79899359 := by decide
private theorem lowerTwo_row_811 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 811 j) = 80579048 := by decide
private theorem lowerTwo_row_812 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 812 j) = 82049463 := by decide
private theorem lowerTwo_row_813 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 813 j) = 82726221 := by decide
private theorem lowerTwo_row_814 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 814 j) = 84193751 := by decide
private theorem lowerTwo_row_815 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 815 j) = 84867611 := by decide
private theorem lowerTwo_row_816 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 816 j) = 86332268 := by decide
private theorem lowerTwo_row_817 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 817 j) = 87795707 := by decide
private theorem lowerTwo_row_818 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 818 j) = 88465031 := by decide
private theorem lowerTwo_row_819 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 819 j) = 89925620 := by decide
private theorem lowerTwo_row_820 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 820 j) = 90592053 := by decide
private theorem lowerTwo_row_821 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 821 j) = 92049811 := by decide
private theorem lowerTwo_row_822 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 822 j) = 92713368 := by decide
private theorem lowerTwo_row_823 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 823 j) = 94168299 := by decide
private theorem lowerTwo_row_824 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 824 j) = 95622020 := by decide
private theorem lowerTwo_row_825 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 825 j) = 96281114 := by decide
private theorem lowerTwo_row_826 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 826 j) = 97732042 := by decide
private theorem lowerTwo_row_827 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 827 j) = 98388294 := by decide
private theorem lowerTwo_row_828 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 828 j) = 99836415 := by decide
private theorem lowerTwo_row_829 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 829 j) = 100489836 := by decide
private theorem lowerTwo_row_830 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 830 j) = 101935187 := by decide
private theorem lowerTwo_row_831 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 831 j) = 103379352 := by decide
private theorem lowerTwo_row_832 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 832 j) = 104028362 := by decide
private theorem lowerTwo_row_833 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 833 j) = 105469760 := by decide
private theorem lowerTwo_row_834 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 834 j) = 106115974 := by decide
private theorem lowerTwo_row_835 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 835 j) = 107554626 := by decide
private theorem lowerTwo_row_836 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 836 j) = 108198046 := by decide
private theorem lowerTwo_row_837 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 837 j) = 109633967 := by decide
private theorem lowerTwo_row_838 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 838 j) = 111068716 := by decide
private theorem lowerTwo_row_839 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 839 j) = 111707783 := by decide
private theorem lowerTwo_row_840 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 840 j) = 113139830 := by decide
private theorem lowerTwo_row_841 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 841 j) = 113776118 := by decide
private theorem lowerTwo_row_842 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 842 j) = 115205463 := by decide
private theorem lowerTwo_row_843 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 843 j) = 115838998 := by decide
private theorem lowerTwo_row_844 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 844 j) = 117265638 := by decide
private theorem lowerTwo_row_845 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 845 j) = 118691138 := by decide
private theorem lowerTwo_row_846 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 846 j) = 119320385 := by decide
private theorem lowerTwo_row_847 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 847 j) = 120743218 := by decide
private theorem lowerTwo_row_848 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 848 j) = 121369739 := by decide
private theorem lowerTwo_row_849 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 849 j) = 122789895 := by decide
private theorem lowerTwo_row_850 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 850 j) = 123413705 := by decide
private theorem lowerTwo_row_851 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 851 j) = 124831209 := by decide
private theorem lowerTwo_row_852 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 852 j) = 126247601 := by decide
private theorem lowerTwo_row_853 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 853 j) = 126867176 := by decide
private theorem lowerTwo_row_854 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 854 j) = 128280932 := by decide
private theorem lowerTwo_row_855 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 855 j) = 128897812 := by decide
private theorem lowerTwo_row_856 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 856 j) = 130308950 := by decide
private theorem lowerTwo_row_857 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 857 j) = 130923145 := by decide
private theorem lowerTwo_row_858 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 858 j) = 132331662 := by decide
private theorem lowerTwo_row_859 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 859 j) = 133739085 := by decide
private theorem lowerTwo_row_860 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 860 j) = 134349114 := by decide
private theorem lowerTwo_row_861 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 861 j) = 135753945 := by decide
private theorem lowerTwo_row_862 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 862 j) = 136361306 := by decide
private theorem lowerTwo_row_863 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 863 j) = 137763555 := by decide
private theorem lowerTwo_row_864 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 864 j) = 138368288 := by decide
private theorem lowerTwo_row_865 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 865 j) = 139767966 := by decide
private theorem lowerTwo_row_866 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 866 j) = 141166569 := by decide
private theorem lowerTwo_row_867 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 867 j) = 141767165 := by decide
private theorem lowerTwo_row_868 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 868 j) = 143163223 := by decide
private theorem lowerTwo_row_869 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 869 j) = 143761202 := by decide
private theorem lowerTwo_row_870 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 870 j) = 145154704 := by decide
private theorem lowerTwo_row_871 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 871 j) = 145750082 := by decide
private theorem lowerTwo_row_872 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 872 j) = 147141056 := by decide
private theorem lowerTwo_row_873 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 873 j) = 148530981 := by decide
private theorem lowerTwo_row_874 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 874 j) = 149122281 := by decide
private theorem lowerTwo_row_875 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 875 j) = 150509701 := by decide
private theorem lowerTwo_row_876 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 876 j) = 151098411 := by decide
private theorem lowerTwo_row_877 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 877 j) = 152483325 := by decide
private theorem lowerTwo_row_878 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 878 j) = 153069465 := by decide
private theorem lowerTwo_row_879 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 879 j) = 154451885 := by decide
private theorem lowerTwo_row_880 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 880 j) = 155833267 := by decide
private theorem lowerTwo_row_881 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 881 j) = 156415396 := by decide
private theorem lowerTwo_row_882 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 882 j) = 157794303 := by decide
private theorem lowerTwo_row_883 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 883 j) = 158373885 := by decide
private theorem lowerTwo_row_884 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 884 j) = 159750320 := by decide
private theorem lowerTwo_row_885 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 885 j) = 160327374 := by decide
private theorem lowerTwo_row_886 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 886 j) = 161701358 := by decide
private theorem lowerTwo_row_887 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 887 j) = 163074337 := by decide
private theorem lowerTwo_row_888 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 888 j) = 163647420 := by decide
private theorem lowerTwo_row_889 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 889 j) = 165017959 := by decide
private theorem lowerTwo_row_890 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 890 j) = 165588531 := by decide
private theorem lowerTwo_row_891 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 891 j) = 166956646 := by decide
private theorem lowerTwo_row_892 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 892 j) = 167524705 := by decide
private theorem lowerTwo_row_893 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 893 j) = 168890403 := by decide
private theorem lowerTwo_row_894 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 894 j) = 170255121 := by decide
private theorem lowerTwo_row_895 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 895 j) = 170819265 := by decide
private theorem lowerTwo_row_896 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 896 j) = 172181573 := by decide
private theorem lowerTwo_row_897 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 897 j) = 172743244 := by decide
private theorem lowerTwo_row_898 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 898 j) = 174103162 := by decide
private theorem lowerTwo_row_899 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 899 j) = 174662358 := by decide
private theorem lowerTwo_row_900 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 900 j) = 176019897 := by decide
private theorem lowerTwo_row_901 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 901 j) = 177376469 := by decide
private theorem lowerTwo_row_902 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 902 j) = 177931808 := by decide
private theorem lowerTwo_row_903 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 903 j) = 179286020 := by decide
private theorem lowerTwo_row_904 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 904 j) = 179838915 := by decide
private theorem lowerTwo_row_905 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 905 j) = 181190767 := by decide
private theorem lowerTwo_row_906 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 906 j) = 181741220 := by decide
private theorem lowerTwo_row_907 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 907 j) = 183090737 := by decide
private theorem lowerTwo_row_908 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 908 j) = 184439285 := by decide
private theorem lowerTwo_row_909 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 909 j) = 184985937 := by decide
private theorem lowerTwo_row_910 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 910 j) = 186332174 := by decide
private theorem lowerTwo_row_911 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 911 j) = 186876414 := by decide
private theorem lowerTwo_row_912 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 912 j) = 188220330 := by decide
private theorem lowerTwo_row_913 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 913 j) = 188762156 := by decide
private theorem lowerTwo_row_914 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 914 j) = 190103762 := by decide
private theorem lowerTwo_row_915 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 915 j) = 191444460 := by decide
private theorem lowerTwo_row_916 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 916 j) = 191982519 := by decide
private theorem lowerTwo_row_917 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 917 j) = 193320915 := by decide
private theorem lowerTwo_row_918 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 918 j) = 193856591 := by decide
private theorem lowerTwo_row_919 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 919 j) = 195192714 := by decide
private theorem lowerTwo_row_920 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 920 j) = 195726025 := by decide
private theorem lowerTwo_row_921 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 921 j) = 197059866 := by decide
private theorem lowerTwo_row_922 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 922 j) = 198392799 := by decide
private theorem lowerTwo_row_923 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 923 j) = 198922387 := by decide
private theorem lowerTwo_row_924 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 924 j) = 200253071 := by decide
private theorem lowerTwo_row_925 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 925 j) = 200780319 := by decide
private theorem lowerTwo_row_926 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 926 j) = 202108748 := by decide
private theorem lowerTwo_row_927 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 927 j) = 202633658 := by decide
private theorem lowerTwo_row_928 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 928 j) = 203959852 := by decide
private theorem lowerTwo_row_929 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 929 j) = 205285157 := by decide
private theorem lowerTwo_row_930 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 930 j) = 205806410 := by decide
private theorem lowerTwo_row_931 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 931 j) = 207129486 := by decide
private theorem lowerTwo_row_932 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 932 j) = 207648401 := by decide
private theorem lowerTwo_row_933 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 933 j) = 208969276 := by decide
private theorem lowerTwo_row_934 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 934 j) = 209485891 := by decide
private theorem lowerTwo_row_935 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 935 j) = 210804576 := by decide
private theorem lowerTwo_row_936 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 936 j) = 212122380 := by decide
private theorem lowerTwo_row_937 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 937 j) = 212635362 := by decide
private theorem lowerTwo_row_938 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 938 j) = 213950986 := by decide
private theorem lowerTwo_row_939 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 939 j) = 214461673 := by decide
private theorem lowerTwo_row_940 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 940 j) = 215775117 := by decide
private theorem lowerTwo_row_941 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 941 j) = 216283553 := by decide
private theorem lowerTwo_row_942 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 942 j) = 217594831 := by decide
private theorem lowerTwo_row_943 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 943 j) = 218905258 := by decide
private theorem lowerTwo_row_944 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 944 j) = 219410097 := by decide
private theorem lowerTwo_row_945 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 945 j) = 220718364 := by decide
private theorem lowerTwo_row_946 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 946 j) = 221220963 := by decide
private theorem lowerTwo_row_947 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 947 j) = 222527098 := by decide
private theorem lowerTwo_row_948 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 948 j) = 223027423 := by decide
private theorem lowerTwo_row_949 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 949 j) = 224331436 := by decide
private theorem lowerTwo_row_950 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 950 j) = 225634594 := by decide
private theorem lowerTwo_row_951 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 951 j) = 226131400 := by decide
private theorem lowerTwo_row_952 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 952 j) = 227432455 := by decide
private theorem lowerTwo_row_953 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 953 j) = 227927035 := by decide
private theorem lowerTwo_row_954 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 954 j) = 229225977 := by decide
private theorem lowerTwo_row_955 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 955 j) = 229718333 := by decide
private theorem lowerTwo_row_956 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 956 j) = 231015188 := by decide
private theorem lowerTwo_row_957 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 957 j) = 232311200 := by decide
private theorem lowerTwo_row_958 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 958 j) = 232800082 := by decide
private theorem lowerTwo_row_959 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 959 j) = 234094012 := by decide
private theorem lowerTwo_row_960 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 960 j) = 234580691 := by decide
private theorem lowerTwo_row_961 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 961 j) = 235872549 := by decide
private theorem lowerTwo_row_962 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 962 j) = 236357039 := by decide
private theorem lowerTwo_row_963 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 963 j) = 237646837 := by decide
private theorem lowerTwo_row_964 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 964 j) = 238935834 := by decide
private theorem lowerTwo_row_965 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 965 j) = 239416874 := by decide
private theorem lowerTwo_row_966 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 966 j) = 240703819 := by decide
private theorem lowerTwo_row_967 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 967 j) = 241182685 := by decide
private theorem lowerTwo_row_968 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 968 j) = 242467606 := by decide
private theorem lowerTwo_row_969 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 969 j) = 242944281 := by decide
private theorem lowerTwo_row_970 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 970 j) = 244227071 := by decide
private theorem lowerTwo_row_971 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 971 j) = 245509018 := by decide
private theorem lowerTwo_row_972 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 972 j) = 245982134 := by decide
private theorem lowerTwo_row_973 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 973 j) = 247261961 := by decide
private theorem lowerTwo_row_974 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 974 j) = 247732800 := by decide
private theorem lowerTwo_row_975 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 975 j) = 249010506 := by decide
private theorem lowerTwo_row_976 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 976 j) = 249479108 := by decide
private theorem lowerTwo_row_977 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 977 j) = 250754688 := by decide
private theorem lowerTwo_row_978 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 978 j) = 252029442 := by decide
private theorem lowerTwo_row_979 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 979 j) = 252494552 := by decide
private theorem lowerTwo_row_980 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 980 j) = 253767206 := by decide
private theorem lowerTwo_row_981 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 981 j) = 254230075 := by decide
private theorem lowerTwo_row_982 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 982 j) = 255500642 := by decide
private theorem lowerTwo_row_983 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 983 j) = 255961292 := by decide
private theorem lowerTwo_row_984 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 984 j) = 257229800 := by decide
private theorem lowerTwo_row_985 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 985 j) = 258497496 := by decide
private theorem lowerTwo_row_986 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 986 j) = 258954652 := by decide
private theorem lowerTwo_row_987 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 987 j) = 260220292 := by decide
private theorem lowerTwo_row_988 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 988 j) = 260675265 := by decide
private theorem lowerTwo_row_989 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 989 j) = 261938846 := by decide
private theorem lowerTwo_row_990 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 990 j) = 262391620 := by decide
private theorem lowerTwo_row_991 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 991 j) = 263653144 := by decide
private theorem lowerTwo_row_992 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 992 j) = 264913900 := by decide
private theorem lowerTwo_row_993 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 993 j) = 265363242 := by decide
private theorem lowerTwo_row_994 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 994 j) = 266621953 := by decide
private theorem lowerTwo_row_995 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 995 j) = 267069137 := by decide
private theorem lowerTwo_row_996 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 996 j) = 268325825 := by decide
private theorem lowerTwo_row_997 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 997 j) = 268770839 := by decide
private theorem lowerTwo_row_998 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 998 j) = 270025508 := by decide
private theorem lowerTwo_row_999 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 999 j) = 271279421 := by decide
private theorem lowerTwo_row_1000 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1000 j) = 271721052 := by decide
private theorem lowerTwo_row_1001 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1001 j) = 272972961 := by decide
private theorem lowerTwo_row_1002 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1002 j) = 273412449 := by decide
private theorem lowerTwo_row_1003 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1003 j) = 274662363 := by decide
private theorem lowerTwo_row_1004 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1004 j) = 275099717 := by decide
private theorem lowerTwo_row_1005 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1005 j) = 276347640 := by decide
private theorem lowerTwo_row_1006 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1006 j) = 277594839 := by decide
private theorem lowerTwo_row_1007 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1007 j) = 278028836 := by decide
private theorem lowerTwo_row_1008 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1008 j) = 279274044 := by decide
private theorem lowerTwo_row_1009 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1009 j) = 279705937 := by decide
private theorem lowerTwo_row_1010 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1010 j) = 280949199 := by decide
private theorem lowerTwo_row_1011 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1011 j) = 281378994 := by decide
private theorem lowerTwo_row_1012 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1012 j) = 282620285 := by decide
private theorem lowerTwo_row_1013 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1013 j) = 283860850 := by decide
private theorem lowerTwo_row_1014 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1014 j) = 284287340 := by decide
private theorem lowerTwo_row_1015 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1015 j) = 285525960 := by decide
private theorem lowerTwo_row_1016 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1016 j) = 285950361 := by decide
private theorem lowerTwo_row_1017 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1017 j) = 287187068 := by decide
private theorem lowerTwo_row_1018 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1018 j) = 287609377 := by decide
private theorem lowerTwo_row_1019 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1019 j) = 288844153 := by decide
private theorem lowerTwo_row_1020 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1020 j) = 290078210 := by decide
private theorem lowerTwo_row_1021 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1021 j) = 290497263 := by decide
private theorem lowerTwo_row_1022 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1022 j) = 291729418 := by decide
private theorem lowerTwo_row_1023 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1023 j) = 292146420 := by decide
private theorem lowerTwo_row_1024 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1024 j) = 292837602 := by decide
private theorem lowerTwo_row_1025 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1025 j) = 292175091 := by decide
private theorem lowerTwo_row_1026 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1026 j) = 292326954 := by decide
private theorem lowerTwo_row_1027 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1027 j) = 292479028 := by decide
private theorem lowerTwo_row_1028 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1028 j) = 291816109 := by decide
private theorem lowerTwo_row_1029 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1029 j) = 291968197 := by decide
private theorem lowerTwo_row_1030 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1030 j) = 291305091 := by decide
private theorem lowerTwo_row_1031 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1031 j) = 291457128 := by decide
private theorem lowerTwo_row_1032 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1032 j) = 290793857 := by decide
private theorem lowerTwo_row_1033 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1033 j) = 290945907 := by decide
private theorem lowerTwo_row_1034 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1034 j) = 291098177 := by decide
private theorem lowerTwo_row_1035 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1035 j) = 290434461 := by decide
private theorem lowerTwo_row_1036 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1036 j) = 290586722 := by decide
private theorem lowerTwo_row_1037 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1037 j) = 289922817 := by decide
private theorem lowerTwo_row_1038 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1038 j) = 290075064 := by decide
private theorem lowerTwo_row_1039 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1039 j) = 289410973 := by decide
private theorem lowerTwo_row_1040 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1040 j) = 289563183 := by decide
private theorem lowerTwo_row_1041 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1041 j) = 289715655 := by decide
private theorem lowerTwo_row_1042 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1042 j) = 289051118 := by decide
private theorem lowerTwo_row_1043 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1043 j) = 289203545 := by decide
private theorem lowerTwo_row_1044 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1044 j) = 288538821 := by decide
private theorem lowerTwo_row_1045 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1045 j) = 288691238 := by decide
private theorem lowerTwo_row_1046 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1046 j) = 288026329 := by decide
private theorem lowerTwo_row_1047 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1047 j) = 288178713 := by decide
private theorem lowerTwo_row_1048 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1048 j) = 288331329 := by decide
private theorem lowerTwo_row_1049 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1049 j) = 287665976 := by decide
private theorem lowerTwo_row_1050 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1050 j) = 287818573 := by decide
private theorem lowerTwo_row_1051 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1051 j) = 287153021 := by decide
private theorem lowerTwo_row_1052 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1052 j) = 287305583 := by decide
private theorem lowerTwo_row_1053 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1053 j) = 286639818 := by decide
private theorem lowerTwo_row_1054 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1054 j) = 286792354 := by decide
private theorem lowerTwo_row_1055 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1055 j) = 286945147 := by decide
private theorem lowerTwo_row_1056 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1056 j) = 286278917 := by decide
private theorem lowerTwo_row_1057 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1057 j) = 286431659 := by decide
private theorem lowerTwo_row_1058 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1058 j) = 285765234 := by decide
private theorem lowerTwo_row_1059 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1059 j) = 285917943 := by decide
private theorem lowerTwo_row_1060 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1060 j) = 285251313 := by decide
private theorem lowerTwo_row_1061 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1061 j) = 285404000 := by decide
private theorem lowerTwo_row_1062 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1062 j) = 285556933 := by decide
private theorem lowerTwo_row_1063 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1063 j) = 284889812 := by decide
private theorem lowerTwo_row_1064 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1064 j) = 285042710 := by decide
private theorem lowerTwo_row_1065 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1065 j) = 284375386 := by decide
private theorem lowerTwo_row_1066 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1066 j) = 284528252 := by decide
private theorem lowerTwo_row_1067 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1067 j) = 283860705 := by decide
private theorem lowerTwo_row_1068 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1068 j) = 284013532 := by decide
private theorem lowerTwo_row_1069 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1069 j) = 284166608 := by decide
private theorem lowerTwo_row_1070 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1070 j) = 283498577 := by decide
private theorem lowerTwo_row_1071 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1071 j) = 283651591 := by decide
private theorem lowerTwo_row_1072 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1072 j) = 282983366 := by decide
private theorem lowerTwo_row_1073 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1073 j) = 283136354 := by decide
private theorem lowerTwo_row_1074 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1074 j) = 282467893 := by decide
private theorem lowerTwo_row_1075 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1075 j) = 282620843 := by decide
private theorem lowerTwo_row_1076 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1076 j) = 282774047 := by decide
private theorem lowerTwo_row_1077 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1077 j) = 282105076 := by decide
private theorem lowerTwo_row_1078 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1078 j) = 282258234 := by decide
private theorem lowerTwo_row_1079 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1079 j) = 281589044 := by decide
private theorem lowerTwo_row_1080 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1080 j) = 281742168 := by decide
private theorem lowerTwo_row_1081 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1081 j) = 281072747 := by decide
private theorem lowerTwo_row_1082 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1082 j) = 281225808 := by decide
private theorem lowerTwo_row_1083 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1083 j) = 281379125 := by decide
private theorem lowerTwo_row_1084 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1084 j) = 280709212 := by decide
private theorem lowerTwo_row_1085 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1085 j) = 280862480 := by decide
private theorem lowerTwo_row_1086 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1086 j) = 280192323 := by decide
private theorem lowerTwo_row_1087 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1087 j) = 280345550 := by decide
private theorem lowerTwo_row_1088 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1088 j) = 279675161 := by decide
private theorem lowerTwo_row_1089 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1089 j) = 279828348 := by decide
private theorem lowerTwo_row_1090 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1090 j) = 279981757 := by decide
private theorem lowerTwo_row_1091 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1091 j) = 279310860 := by decide
private theorem lowerTwo_row_1092 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1092 j) = 279464226 := by decide
private theorem lowerTwo_row_1093 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1093 j) = 277969163 := by decide
private theorem lowerTwo_row_1094 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1094 j) = 277298408 := by decide
private theorem lowerTwo_row_1095 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1095 j) = 275805303 := by decide
private theorem lowerTwo_row_1096 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1096 j) = 275134958 := by decide
private theorem lowerTwo_row_1097 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1097 j) = 273643816 := by decide
private theorem lowerTwo_row_1098 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1098 j) = 272973897 := by decide
private theorem lowerTwo_row_1099 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1099 j) = 271484688 := by decide
private theorem lowerTwo_row_1100 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1100 j) = 270815178 := by decide
private theorem lowerTwo_row_1101 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1101 j) = 269327923 := by decide
private theorem lowerTwo_row_1102 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1102 j) = 268658841 := by decide
private theorem lowerTwo_row_1103 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1103 j) = 267173483 := by decide
private theorem lowerTwo_row_1104 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1104 j) = 266504807 := by decide
private theorem lowerTwo_row_1105 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1105 j) = 265021385 := by decide
private theorem lowerTwo_row_1106 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1106 j) = 264353117 := by decide
private theorem lowerTwo_row_1107 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1107 j) = 262871613 := by decide
private theorem lowerTwo_row_1108 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1108 j) = 262203731 := by decide
private theorem lowerTwo_row_1109 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1109 j) = 260724119 := by decide
private theorem lowerTwo_row_1110 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1110 j) = 260056648 := by decide
private theorem lowerTwo_row_1111 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1111 j) = 258578936 := by decide
private theorem lowerTwo_row_1112 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1112 j) = 257911853 := by decide
private theorem lowerTwo_row_1113 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1113 j) = 256436037 := by decide
private theorem lowerTwo_row_1114 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1114 j) = 255769336 := by decide
private theorem lowerTwo_row_1115 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1115 j) = 254770756 := by decide
private theorem lowerTwo_row_1116 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1116 j) = 275007892 := by decide
private theorem lowerTwo_row_1117 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1117 j) = 275634999 := by decide
private theorem lowerTwo_row_1118 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1118 j) = 276261449 := by decide
private theorem lowerTwo_row_1119 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1119 j) = 276058153 := by decide
private theorem lowerTwo_row_1120 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1120 j) = 276682788 := by decide
private theorem lowerTwo_row_1121 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1121 j) = 276477479 := by decide
private theorem lowerTwo_row_1122 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1122 j) = 277100307 := by decide
private theorem lowerTwo_row_1123 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1123 j) = 276892995 := by decide
private theorem lowerTwo_row_1124 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1124 j) = 277514057 := by decide
private theorem lowerTwo_row_1125 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1125 j) = 278134501 := by decide
private theorem lowerTwo_row_1126 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1126 j) = 277924058 := by decide
private theorem lowerTwo_row_1127 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1127 j) = 278542722 := by decide
private theorem lowerTwo_row_1128 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1128 j) = 278330299 := by decide
private theorem lowerTwo_row_1129 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1129 j) = 278947201 := by decide
private theorem lowerTwo_row_1130 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1130 j) = 278732812 := by decide
private theorem lowerTwo_row_1131 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1131 j) = 279347962 := by decide
private theorem lowerTwo_row_1132 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1132 j) = 279962526 := by decide
private theorem lowerTwo_row_1133 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1133 j) = 279745001 := by decide
private theorem lowerTwo_row_1134 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1134 j) = 280357803 := by decide
private theorem lowerTwo_row_1135 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1135 j) = 280138318 := by decide
private theorem lowerTwo_row_1136 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1136 j) = 280749377 := by decide
private theorem lowerTwo_row_1137 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1137 j) = 280527937 := by decide
private theorem lowerTwo_row_1138 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1138 j) = 281137263 := by decide
private theorem lowerTwo_row_1139 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1139 j) = 281746006 := by decide
private theorem lowerTwo_row_1140 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1140 j) = 281521450 := by decide
private theorem lowerTwo_row_1141 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1141 j) = 282128451 := by decide
private theorem lowerTwo_row_1142 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1142 j) = 281901971 := by decide
private theorem lowerTwo_row_1143 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1143 j) = 282507238 := by decide
private theorem lowerTwo_row_1144 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1144 j) = 282278809 := by decide
private theorem lowerTwo_row_1145 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1145 j) = 282882361 := by decide
private theorem lowerTwo_row_1146 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1146 j) = 283485317 := by decide
private theorem lowerTwo_row_1147 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1147 j) = 283253745 := by decide
private theorem lowerTwo_row_1148 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1148 j) = 283854923 := by decide
private theorem lowerTwo_row_1149 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1149 j) = 283621335 := by decide
private theorem lowerTwo_row_1150 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1150 j) = 284220704 := by decide
private theorem lowerTwo_row_1151 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1151 j) = 283985104 := by decide
private theorem lowerTwo_row_1152 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1152 j) = 284582688 := by decide
private theorem lowerTwo_row_1153 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1153 j) = 285179644 := by decide
private theorem lowerTwo_row_1154 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1154 j) = 284940848 := by decide
private theorem lowerTwo_row_1155 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1155 j) = 285536053 := by decide
private theorem lowerTwo_row_1156 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1156 j) = 285295259 := by decide
private theorem lowerTwo_row_1157 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1157 j) = 285888670 := by decide
private theorem lowerTwo_row_1158 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1158 j) = 285645885 := by decide
private theorem lowerTwo_row_1159 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1159 j) = 286237523 := by decide
private theorem lowerTwo_row_1160 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1160 j) = 286828561 := by decide
private theorem lowerTwo_row_1161 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1161 j) = 286582593 := by decide
private theorem lowerTwo_row_1162 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1162 j) = 287171871 := by decide
private theorem lowerTwo_row_1163 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1163 j) = 286923925 := by decide
private theorem lowerTwo_row_1164 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1164 j) = 287511447 := by decide
private theorem lowerTwo_row_1165 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1165 j) = 287261524 := by decide
private theorem lowerTwo_row_1166 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1166 j) = 287847278 := by decide
private theorem lowerTwo_row_1167 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1167 j) = 288432453 := by decide
private theorem lowerTwo_row_1168 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1168 j) = 288179381 := by decide
private theorem lowerTwo_row_1169 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1169 j) = 288762806 := by decide
private theorem lowerTwo_row_1170 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1170 j) = 288507760 := by decide
private theorem lowerTwo_row_1171 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1171 j) = 289089434 := by decide
private theorem lowerTwo_row_1172 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1172 j) = 288832423 := by decide
private theorem lowerTwo_row_1173 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1173 j) = 289412378 := by decide
private theorem lowerTwo_row_1174 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1174 j) = 289991741 := by decide
private theorem lowerTwo_row_1175 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1175 j) = 289731594 := by decide
private theorem lowerTwo_row_1176 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1176 j) = 290309241 := by decide
private theorem lowerTwo_row_1177 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1177 j) = 290047139 := by decide
private theorem lowerTwo_row_1178 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1178 j) = 290623066 := by decide
private theorem lowerTwo_row_1179 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1179 j) = 290358989 := by decide
private theorem lowerTwo_row_1180 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1180 j) = 290933188 := by decide
private theorem lowerTwo_row_1181 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1181 j) = 291506831 := by decide
private theorem lowerTwo_row_1182 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1182 j) = 291239659 := by decide
private theorem lowerTwo_row_1183 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1183 j) = 291811584 := by decide
private theorem lowerTwo_row_1184 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1184 j) = 291542459 := by decide
private theorem lowerTwo_row_1185 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1185 j) = 292112688 := by decide
private theorem lowerTwo_row_1186 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1186 j) = 291841599 := by decide
private theorem lowerTwo_row_1187 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1187 j) = 292410138 := by decide
private theorem lowerTwo_row_1188 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1188 j) = 292978098 := by decide
private theorem lowerTwo_row_1189 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1189 j) = 292703945 := by decide
private theorem lowerTwo_row_1190 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1190 j) = 293270198 := by decide
private theorem lowerTwo_row_1191 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1191 j) = 292994115 := by decide
private theorem lowerTwo_row_1192 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1192 j) = 293558695 := by decide
private theorem lowerTwo_row_1193 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1193 j) = 293280670 := by decide
private theorem lowerTwo_row_1194 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1194 j) = 293843569 := by decide
private theorem lowerTwo_row_1195 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1195 j) = 294405912 := by decide
private theorem lowerTwo_row_1196 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1196 j) = 294124830 := by decide
private theorem lowerTwo_row_1197 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1197 j) = 294685494 := by decide
private theorem lowerTwo_row_1198 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1198 j) = 294402479 := by decide
private theorem lowerTwo_row_1199 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1199 j) = 294961478 := by decide
private theorem lowerTwo_row_1200 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1200 j) = 294676538 := by decide
private theorem lowerTwo_row_1201 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1201 j) = 295233877 := by decide
private theorem lowerTwo_row_1202 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1202 j) = 295790667 := by decide
private theorem lowerTwo_row_1203 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1203 j) = 295502686 := by decide
private theorem lowerTwo_row_1204 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1204 j) = 296057825 := by decide
private theorem lowerTwo_row_1205 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1205 j) = 295767902 := by decide
private theorem lowerTwo_row_1206 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1206 j) = 296321337 := by decide
private theorem lowerTwo_row_1207 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1207 j) = 296029427 := by decide
private theorem lowerTwo_row_1208 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1208 j) = 296581105 := by decide
private theorem lowerTwo_row_1209 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1209 j) = 297132213 := by decide
private theorem lowerTwo_row_1210 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1210 j) = 296837137 := by decide
private theorem lowerTwo_row_1211 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1211 j) = 297386507 := by decide
private theorem lowerTwo_row_1212 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1212 j) = 297089435 := by decide
private theorem lowerTwo_row_1213 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1213 j) = 297637058 := by decide
private theorem lowerTwo_row_1214 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1214 j) = 297338008 := by decide
private theorem lowerTwo_row_1215 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1215 j) = 297883910 := by decide
private theorem lowerTwo_row_1216 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1216 j) = 298429250 := by decide
private theorem lowerTwo_row_1217 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1217 j) = 298127034 := by decide
private theorem lowerTwo_row_1218 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1218 j) = 298670655 := by decide
private theorem lowerTwo_row_1219 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1219 j) = 298366455 := by decide
private theorem lowerTwo_row_1220 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1220 j) = 298908358 := by decide
private theorem lowerTwo_row_1221 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1221 j) = 298602182 := by decide
private theorem lowerTwo_row_1222 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1222 j) = 299142376 := by decide
private theorem lowerTwo_row_1223 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1223 j) = 299681995 := by decide
private theorem lowerTwo_row_1224 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1224 j) = 299372691 := by decide
private theorem lowerTwo_row_1225 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1225 j) = 299910628 := by decide
private theorem lowerTwo_row_1226 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1226 j) = 299599343 := by decide
private theorem lowerTwo_row_1227 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1227 j) = 300135571 := by decide
private theorem lowerTwo_row_1228 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1228 j) = 299822305 := by decide
private theorem lowerTwo_row_1229 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1229 j) = 300356863 := by decide
private theorem lowerTwo_row_1230 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1230 j) = 300890857 := by decide
private theorem lowerTwo_row_1231 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1231 j) = 300574474 := by decide
private theorem lowerTwo_row_1232 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1232 j) = 301106775 := by decide
private theorem lowerTwo_row_1233 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1233 j) = 300788454 := by decide
private theorem lowerTwo_row_1234 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1234 j) = 301319075 := by decide
private theorem lowerTwo_row_1235 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1235 j) = 300998791 := by decide
private theorem lowerTwo_row_1236 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1236 j) = 301527714 := by decide
private theorem lowerTwo_row_1237 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1237 j) = 302056108 := by decide
private theorem lowerTwo_row_1238 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1238 j) = 301732739 := by decide
private theorem lowerTwo_row_1239 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1239 j) = 302259451 := by decide
private theorem lowerTwo_row_1240 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1240 j) = 301934127 := by decide
private theorem lowerTwo_row_1241 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1241 j) = 302459183 := by decide
private theorem lowerTwo_row_1242 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1242 j) = 302131922 := by decide
private theorem lowerTwo_row_1243 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1243 j) = 302655300 := by decide
private theorem lowerTwo_row_1244 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1244 j) = 303178163 := by decide
private theorem lowerTwo_row_1245 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1245 j) = 302847820 := by decide
private theorem lowerTwo_row_1246 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1246 j) = 303369023 := by decide
private theorem lowerTwo_row_1247 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1247 j) = 303036733 := by decide
private theorem lowerTwo_row_1248 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1248 j) = 303556276 := by decide
private theorem lowerTwo_row_1249 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1249 j) = 303222059 := by decide
private theorem lowerTwo_row_1250 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1250 j) = 303739964 := by decide
private theorem lowerTwo_row_1251 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1251 j) = 304257328 := by decide
private theorem lowerTwo_row_1252 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1252 j) = 303920060 := by decide
private theorem lowerTwo_row_1253 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1253 j) = 304435804 := by decide
private theorem lowerTwo_row_1254 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1254 j) = 304096592 := by decide
private theorem lowerTwo_row_1255 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1255 j) = 304610696 := by decide
private theorem lowerTwo_row_1256 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1256 j) = 304269595 := by decide
private theorem lowerTwo_row_1257 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1257 j) = 304782072 := by decide
private theorem lowerTwo_row_1258 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1258 j) = 305294036 := by decide
private theorem lowerTwo_row_1259 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1259 j) = 304949882 := by decide
private theorem lowerTwo_row_1260 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1260 j) = 305460229 := by decide
private theorem lowerTwo_row_1261 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1261 j) = 305114153 := by decide
private theorem lowerTwo_row_1262 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1262 j) = 305622883 := by decide
private theorem lowerTwo_row_1263 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1263 j) = 305274894 := by decide
private theorem lowerTwo_row_1264 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1264 j) = 305782006 := by decide
private theorem lowerTwo_row_1265 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1265 j) = 306288634 := by decide
private theorem lowerTwo_row_1266 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1266 j) = 305937621 := by decide
private theorem lowerTwo_row_1267 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1267 j) = 306442619 := by decide
private theorem lowerTwo_row_1268 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1268 j) = 306089658 := by decide
private theorem lowerTwo_row_1269 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1269 j) = 306592971 := by decide
private theorem lowerTwo_row_1270 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1270 j) = 306237982 := by decide
private theorem lowerTwo_row_1271 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1271 j) = 306739585 := by decide
private theorem lowerTwo_row_1272 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1272 j) = 307240634 := by decide
private theorem lowerTwo_row_1273 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1273 j) = 306882490 := by decide
private theorem lowerTwo_row_1274 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1274 j) = 307381847 := by decide
private theorem lowerTwo_row_1275 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1275 j) = 307021725 := by decide
private theorem lowerTwo_row_1276 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1276 j) = 307519377 := by decide
private theorem lowerTwo_row_1277 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1277 j) = 307157249 := by decide
private theorem lowerTwo_row_1278 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1278 j) = 307653220 := by decide
private theorem lowerTwo_row_1279 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1279 j) = 308148655 := by decide
private theorem lowerTwo_row_1280 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1280 j) = 307783376 := by decide
private theorem lowerTwo_row_1281 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1281 j) = 308277129 := by decide
private theorem lowerTwo_row_1282 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1282 j) = 307909883 := by decide
private theorem lowerTwo_row_1283 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1283 j) = 308401947 := by decide
private theorem lowerTwo_row_1284 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1284 j) = 308032693 := by decide
private theorem lowerTwo_row_1285 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1285 j) = 308523098 := by decide
private theorem lowerTwo_row_1286 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1286 j) = 309012961 := by decide
private theorem lowerTwo_row_1287 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1287 j) = 308640599 := by decide
private theorem lowerTwo_row_1288 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1288 j) = 309128794 := by decide
private theorem lowerTwo_row_1289 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1289 j) = 308754437 := by decide
private theorem lowerTwo_row_1290 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1290 j) = 309240980 := by decide
private theorem lowerTwo_row_1291 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1291 j) = 308864655 := by decide
private theorem lowerTwo_row_1292 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1292 j) = 309349538 := by decide
private theorem lowerTwo_row_1293 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1293 j) = 309833895 := by decide
private theorem lowerTwo_row_1294 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1294 j) = 309454448 := by decide
private theorem lowerTwo_row_1295 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1295 j) = 309937168 := by decide
private theorem lowerTwo_row_1296 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1296 j) = 309555753 := by decide
private theorem lowerTwo_row_1297 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1297 j) = 310036813 := by decide
private theorem lowerTwo_row_1298 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1298 j) = 309653435 := by decide
private theorem lowerTwo_row_1299 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1299 j) = 310132832 := by decide
private theorem lowerTwo_row_1300 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1300 j) = 310611745 := by decide
private theorem lowerTwo_row_1301 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1301 j) = 310225278 := by decide
private theorem lowerTwo_row_1302 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1302 j) = 310702541 := by decide
private theorem lowerTwo_row_1303 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1303 j) = 310314095 := by decide
private theorem lowerTwo_row_1304 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1304 j) = 310789721 := by decide
private theorem lowerTwo_row_1305 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1305 j) = 310399320 := by decide
private theorem lowerTwo_row_1306 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1306 j) = 310873329 := by decide
private theorem lowerTwo_row_1307 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1307 j) = 311346821 := by decide
private theorem lowerTwo_row_1308 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1308 j) = 310953332 := by decide
private theorem lowerTwo_row_1309 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1309 j) = 311425217 := by decide
private theorem lowerTwo_row_1310 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1310 j) = 311029768 := by decide
private theorem lowerTwo_row_1311 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1311 j) = 311500031 := by decide
private theorem lowerTwo_row_1312 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1312 j) = 311102637 := by decide
private theorem lowerTwo_row_1313 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1313 j) = 311571277 := by decide
private theorem lowerTwo_row_1314 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1314 j) = 312039411 := by decide
private theorem lowerTwo_row_1315 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1315 j) = 311638959 := by decide
private theorem lowerTwo_row_1316 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1316 j) = 312105475 := by decide
private theorem lowerTwo_row_1317 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1317 j) = 311703083 := by decide
private theorem lowerTwo_row_1318 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1318 j) = 312168000 := by decide
private theorem lowerTwo_row_1319 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1319 j) = 311763667 := by decide
private theorem lowerTwo_row_1320 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1320 j) = 312226970 := by decide
private theorem lowerTwo_row_1321 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1321 j) = 312689807 := by decide
private theorem lowerTwo_row_1322 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1322 j) = 312282401 := by decide
private theorem lowerTwo_row_1323 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1323 j) = 312743638 := by decide
private theorem lowerTwo_row_1324 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1324 j) = 312334301 := by decide
private theorem lowerTwo_row_1325 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1325 j) = 312793925 := by decide
private theorem lowerTwo_row_1326 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1326 j) = 312382686 := by decide
private theorem lowerTwo_row_1327 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1327 j) = 312840709 := by decide
private theorem lowerTwo_row_1328 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1328 j) = 313298275 := by decide
private theorem lowerTwo_row_1329 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1329 j) = 312883973 := by decide
private theorem lowerTwo_row_1330 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1330 j) = 313339939 := by decide
private theorem lowerTwo_row_1331 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1331 j) = 312923717 := by decide
private theorem lowerTwo_row_1332 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1332 j) = 313378093 := by decide
private theorem lowerTwo_row_1333 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1333 j) = 312959890 := by decide
private theorem lowerTwo_row_1334 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1334 j) = 313412585 := by decide
private theorem lowerTwo_row_1335 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1335 j) = 314296460 := by decide
private theorem lowerTwo_row_1336 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1336 j) = 313874864 := by decide
private theorem lowerTwo_row_1337 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1337 j) = 314756918 := by decide
private theorem lowerTwo_row_1338 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1338 j) = 314765134 := by decide
private theorem lowerTwo_row_1339 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1339 j) = 315645628 := by decide
private theorem lowerTwo_row_1340 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1340 j) = 315651939 := by decide
private theorem lowerTwo_row_1341 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1341 j) = 316098088 := by decide
private theorem lowerTwo_row_1342 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1342 j) = 316976354 := by decide
private theorem lowerTwo_row_1343 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1343 j) = 316979417 := by decide
private theorem lowerTwo_row_1344 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1344 j) = 317856132 := by decide
private theorem lowerTwo_row_1345 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1345 j) = 317857309 := by decide
private theorem lowerTwo_row_1346 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1346 j) = 318298842 := by decide
private theorem lowerTwo_row_1347 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1347 j) = 318297898 := by decide
private theorem lowerTwo_row_1348 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1348 j) = 319171283 := by decide
private theorem lowerTwo_row_1349 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1349 j) = 320044259 := by decide
private theorem lowerTwo_row_1350 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1350 j) = 320040333 := by decide
private theorem lowerTwo_row_1351 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1351 j) = 320477254 := by decide
private theorem lowerTwo_row_1352 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1352 j) = 320471193 := by decide
private theorem lowerTwo_row_1353 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1353 j) = 321340848 := by decide
private theorem lowerTwo_row_1354 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1354 j) = 321332928 := by decide
private theorem lowerTwo_row_1355 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1355 j) = 322201090 := by decide
private theorem lowerTwo_row_1356 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1356 j) = 322633474 := by decide
private theorem lowerTwo_row_1357 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1357 j) = 322622326 := by decide
private theorem lowerTwo_row_1358 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1358 j) = 323488285 := by decide
private theorem lowerTwo_row_1359 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1359 j) = 323475280 := by decide
private theorem lowerTwo_row_1360 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1360 j) = 324339772 := by decide
private theorem lowerTwo_row_1361 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1361 j) = 323888687 := by decide
private theorem lowerTwo_row_1362 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1362 j) = 324751380 := by decide
private theorem lowerTwo_row_1363 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1363 j) = 325613710 := by decide
private theorem lowerTwo_row_1364 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1364 j) = 325638499 := by decide
private theorem lowerTwo_row_1365 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1365 j) = 326542423 := by decide
private theorem lowerTwo_row_1366 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1366 j) = 326171543 := by decide
private theorem lowerTwo_row_1367 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1367 j) = 327074187 := by decide
private theorem lowerTwo_row_1368 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1368 j) = 327096017 := by decide
private theorem lowerTwo_row_1369 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1369 j) = 328040429 := by decide
private theorem lowerTwo_row_1370 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1370 j) = 328941947 := by decide
private theorem lowerTwo_row_1371 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1371 j) = 328523587 := by decide
private theorem lowerTwo_row_1372 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1372 j) = 329466588 := by decide
private theorem lowerTwo_row_1373 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1373 j) = 329484612 := by decide
private theorem lowerTwo_row_1374 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1374 j) = 330383891 := by decide
private theorem lowerTwo_row_1375 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1375 j) = 330443311 := by decide
private theorem lowerTwo_row_1376 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1376 j) = 330902745 := by decide
private theorem lowerTwo_row_1377 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1377 j) = 331800604 := by decide
private theorem lowerTwo_row_1378 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1378 j) = 331857567 := by decide
private theorem lowerTwo_row_1379 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1379 j) = 332754473 := by decide
private theorem lowerTwo_row_1380 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1380 j) = 332767354 := by decide
private theorem lowerTwo_row_1381 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1381 j) = 333266242 := by decide
private theorem lowerTwo_row_1382 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1382 j) = 333277543 := by decide
private theorem lowerTwo_row_1383 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1383 j) = 334172243 := by decide
private theorem lowerTwo_row_1384 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1384 j) = 335109495 := by decide
private theorem lowerTwo_row_1385 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1385 j) = 335118627 := by decide
private theorem lowerTwo_row_1386 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1386 j) = 335571574 := by decide
private theorem lowerTwo_row_1387 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1387 j) = 335621752 := by decide
private theorem lowerTwo_row_1388 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1388 j) = 336514105 := by decide
private theorem lowerTwo_row_1389 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1389 j) = 336520266 := by decide
private theorem lowerTwo_row_1390 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1390 j) = 337454275 := by decide
private theorem lowerTwo_row_1391 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1391 j) = 337904046 := by decide
private theorem lowerTwo_row_1392 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1392 j) = 337907751 := by decide
private theorem lowerTwo_row_1393 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1393 j) = 338840398 := by decide
private theorem lowerTwo_row_1394 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1394 j) = 338842754 := by decide
private theorem lowerTwo_row_1395 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1395 j) = 339731768 := by decide
private theorem lowerTwo_row_1396 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1396 j) = 339333099 := by decide
private theorem lowerTwo_row_1397 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1397 j) = 340220913 := by decide
private theorem lowerTwo_row_1398 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1398 j) = 341108571 := by decide
private theorem lowerTwo_row_1399 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1399 j) = 341149748 := by decide
private theorem lowerTwo_row_1400 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1400 j) = 342036458 := by decide
private theorem lowerTwo_row_1401 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1401 j) = 341590536 := by decide
private theorem lowerTwo_row_1402 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1402 j) = 342518624 := by decide
private theorem lowerTwo_row_1403 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1403 j) = 342514249 := by decide
private theorem lowerTwo_row_1404 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1404 j) = 343398758 := by decide
private theorem lowerTwo_row_1405 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1405 j) = 344325736 := by decide
private theorem lowerTwo_row_1406 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1406 j) = 343875214 := by decide
private theorem lowerTwo_row_1407 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1407 j) = 344758388 := by decide
private theorem lowerTwo_row_1408 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1408 j) = 344792822 := by decide
private theorem lowerTwo_row_1409 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1409 j) = 345675072 := by decide
private theorem lowerTwo_row_1410 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1410 j) = 345665574 := by decide
private theorem lowerTwo_row_1411 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1411 j) = 346144565 := by decide
private theorem lowerTwo_row_1412 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1412 j) = 347025496 := by decide
private theorem lowerTwo_row_1413 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1413 j) = 347013576 := by decide
private theorem lowerTwo_row_1414 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1414 j) = 347936084 := by decide
private theorem lowerTwo_row_1415 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1415 j) = 347922854 := by decide
private theorem lowerTwo_row_1416 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1416 j) = 348356160 := by decide
private theorem lowerTwo_row_1417 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1417 j) = 348383860 := by decide
private theorem lowerTwo_row_1418 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1418 j) = 349261705 := by decide
private theorem lowerTwo_row_1419 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1419 j) = 350139428 := by decide
private theorem lowerTwo_row_1420 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1420 j) = 350164938 := by decide
private theorem lowerTwo_row_1421 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1421 j) = 350595167 := by decide
private theorem lowerTwo_row_1422 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1422 j) = 350576588 := by decide
private theorem lowerTwo_row_1423 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1423 j) = 351494675 := by decide
private theorem lowerTwo_row_1424 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1424 j) = 351474795 := by decide
private theorem lowerTwo_row_1425 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1425 j) = 352349462 := by decide
private theorem lowerTwo_row_1426 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1426 j) = 352819060 := by decide
private theorem lowerTwo_row_1427 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1427 j) = 352796773 := by decide
private theorem lowerTwo_row_1428 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1428 j) = 353670142 := by decide
private theorem lowerTwo_row_1429 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1429 j) = 353688970 := by decide
private theorem lowerTwo_row_1430 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1430 j) = 354561479 := by decide
private theorem lowerTwo_row_1431 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1431 j) = 354088164 := by decide
private theorem lowerTwo_row_1432 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1432 j) = 355001916 := by decide
private theorem lowerTwo_row_1433 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1433 j) = 355873125 := by decide
private theorem lowerTwo_row_1434 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1434 j) = 355845771 := by decide
private theorem lowerTwo_row_1435 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1435 j) = 356758475 := by decide
private theorem lowerTwo_row_1436 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1436 j) = 356280607 := by decide
private theorem lowerTwo_row_1437 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1437 j) = 357149703 := by decide
private theorem lowerTwo_row_1438 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1438 j) = 357161878 := by decide
private theorem lowerTwo_row_1439 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1439 j) = 358030091 := by decide
private theorem lowerTwo_row_1440 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1440 j) = 358898216 := by decide
private theorem lowerTwo_row_1441 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1441 j) = 358458128 := by decide
private theorem lowerTwo_row_1442 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1442 j) = 359325078 := by decide
private theorem lowerTwo_row_1443 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1443 j) = 359291126 := by decide
private theorem lowerTwo_row_1444 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1444 j) = 360199544 := by decide
private theorem lowerTwo_row_1445 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1445 j) = 360164313 := by decide
private theorem lowerTwo_row_1446 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1446 j) = 360578433 := by decide
private theorem lowerTwo_row_1447 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1447 j) = 361485625 := by decide
private theorem lowerTwo_row_1448 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1448 j) = 361447983 := by decide
private theorem lowerTwo_row_1449 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1449 j) = 362311890 := by decide
private theorem lowerTwo_row_1450 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1450 j) = 362315270 := by decide
private theorem lowerTwo_row_1451 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1451 j) = 362726404 := by decide
private theorem lowerTwo_row_1452 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1452 j) = 362685868 := by decide
private theorem lowerTwo_row_1453 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1453 j) = 363590073 := by decide
private theorem lowerTwo_row_1454 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1454 j) = 364451903 := by decide
private theorem lowerTwo_row_1455 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1455 j) = 364409231 := by decide
private theorem lowerTwo_row_1456 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1456 j) = 364859665 := by decide
private theorem lowerTwo_row_1457 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1457 j) = 364815431 := by decide
private theorem lowerTwo_row_1458 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1458 j) = 365675199 := by decide
private theorem lowerTwo_row_1459 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1459 j) = 365671965 := by decide
private theorem lowerTwo_row_1460 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1460 j) = 366530875 := by decide
private theorem lowerTwo_row_1461 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1461 j) = 366935965 := by decide
private theorem lowerTwo_row_1462 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1462 j) = 366930372 := by decide
private theorem lowerTwo_row_1463 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1463 j) = 367788040 := by decide
private theorem lowerTwo_row_1464 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1464 j) = 367738820 := by decide
private theorem lowerTwo_row_1465 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1465 j) = 368637923 := by decide
private theorem lowerTwo_row_1466 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1466 j) = 368132790 := by decide
private theorem lowerTwo_row_1467 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1467 j) = 368988439 := by decide
private theorem lowerTwo_row_1468 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1468 j) = 369886326 := by decide
private theorem lowerTwo_row_1469 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1469 j) = 369833449 := by decide
private theorem lowerTwo_row_1470 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1470 j) = 370688174 := by decide
private theorem lowerTwo_row_1471 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1471 j) = 370220717 := by decide
private theorem lowerTwo_row_1472 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1472 j) = 371074293 := by decide
private theorem lowerTwo_row_1473 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1473 j) = 371018561 := by decide
private theorem lowerTwo_row_1474 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1474 j) = 371913548 := by decide
private theorem lowerTwo_row_1475 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1475 j) = 372766254 := by decide
private theorem lowerTwo_row_1476 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1476 j) = 372251909 := by decide
private theorem lowerTwo_row_1477 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1477 j) = 373145700 := by decide
private theorem lowerTwo_row_1478 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1478 j) = 373086295 := by decide
private theorem lowerTwo_row_1479 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1479 j) = 373936998 := by decide
private theorem lowerTwo_row_1480 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1480 j) = 373918525 := by decide
private theorem lowerTwo_row_1481 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1481 j) = 374310949 := by decide
private theorem lowerTwo_row_1482 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1482 j) = 375160496 := by decide
private theorem lowerTwo_row_1483 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1483 j) = 375139633 := by decide
private theorem lowerTwo_row_1484 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1484 j) = 375988339 := by decide
private theorem lowerTwo_row_1485 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1485 j) = 375923975 := by decide
private theorem lowerTwo_row_1486 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1486 j) = 376355631 := by decide
private theorem lowerTwo_row_1487 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1487 j) = 376289717 := by decide
private theorem lowerTwo_row_1488 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1488 j) = 377136436 := by decide
private theorem lowerTwo_row_1489 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1489 j) = 378025318 := by decide
private theorem lowerTwo_row_1490 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1490 j) = 377957305 := by decide
private theorem lowerTwo_row_1491 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1491 j) = 378343829 := by decide
private theorem lowerTwo_row_1492 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1492 j) = 378316429 := by decide
private theorem lowerTwo_row_1493 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1493 j) = 379161181 := by decide
private theorem lowerTwo_row_1494 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1494 j) = 379090313 := by decide
private theorem lowerTwo_row_1495 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1495 j) = 379976365 := by decide
private theorem lowerTwo_row_1496 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1496 j) = 380359974 := by decide
private theorem lowerTwo_row_1497 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1497 j) = 380286758 := by decide
private theorem lowerTwo_row_1498 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1498 j) = 381171630 := by decide
private theorem lowerTwo_row_1499 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1499 j) = 381097157 := by decide
private theorem lowerTwo_row_1500 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1500 j) = 381939085 := by decide
private theorem lowerTwo_row_1501 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1501 j) = 381444203 := by decide
private theorem lowerTwo_row_1502 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1502 j) = 382285010 := by decide
private theorem lowerTwo_row_1503 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1503 j) = 383125823 := by decide
private theorem lowerTwo_row_1504 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1504 j) = 383089792 := by decide
private theorem lowerTwo_row_1505 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1505 j) = 383929780 := by decide
private theorem lowerTwo_row_1506 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1506 j) = 383388156 := by decide
private theorem lowerTwo_row_1507 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1507 j) = 384269140 := by decide
private theorem lowerTwo_row_1508 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1508 j) = 384188145 := by decide
private theorem lowerTwo_row_1509 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1509 j) = 385026219 := by decide
private theorem lowerTwo_row_1510 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1510 j) = 385906331 := by decide
private theorem lowerTwo_row_1511 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1511 j) = 385360115 := by decide
private theorem lowerTwo_row_1512 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1512 j) = 386197044 := by decide
private theorem lowerTwo_row_1513 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1513 j) = 386154522 := by decide
private theorem lowerTwo_row_1514 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1514 j) = 386990640 := by decide
private theorem lowerTwo_row_1515 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1515 j) = 386904758 := by decide
private theorem lowerTwo_row_1516 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1516 j) = 387317976 := by decide
private theorem lowerTwo_row_1517 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1517 j) = 388152991 := by decide
private theorem lowerTwo_row_1518 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1518 j) = 388064758 := by decide
private theorem lowerTwo_row_1519 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1519 j) = 388941022 := by decide
private theorem lowerTwo_row_1520 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1520 j) = 388851502 := by decide
private theorem lowerTwo_row_1521 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1521 j) = 389219761 := by decide
private theorem lowerTwo_row_1522 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1522 j) = 389170732 := by decide
private theorem lowerTwo_row_1523 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1523 j) = 390003055 := by decide
private theorem lowerTwo_row_1524 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1524 j) = 390835367 := by decide
private theorem lowerTwo_row_1525 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1525 j) = 390784226 := by decide
private theorem lowerTwo_row_1526 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1526 j) = 391149636 := by decide
private theorem lowerTwo_row_1527 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1527 j) = 391054895 := by decide
private theorem lowerTwo_row_1528 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1528 j) = 391927309 := by decide
private theorem lowerTwo_row_1529 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1529 j) = 391831284 := by decide
private theorem lowerTwo_row_1530 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1530 j) = 392660859 := by decide
private theorem lowerTwo_row_1531 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1531 j) = 393065374 := by decide
private theorem lowerTwo_row_1532 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1532 j) = 392966987 := by decide
private theorem lowerTwo_row_1533 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1533 j) = 393795478 := by decide
private theorem lowerTwo_row_1534 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1534 j) = 393737768 := by decide
private theorem lowerTwo_row_1535 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1535 j) = 394565420 := by decide
private theorem lowerTwo_row_1536 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1536 j) = 393996592 := by decide
private theorem lowerTwo_row_1537 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1537 j) = 394865552 := by decide
private theorem lowerTwo_row_1538 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1538 j) = 395692847 := by decide
private theorem lowerTwo_row_1539 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1539 j) = 395590505 := by decide
private theorem lowerTwo_row_1540 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1540 j) = 396459559 := by decide
private theorem lowerTwo_row_1541 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1541 j) = 395887621 := by decide
private theorem lowerTwo_row_1542 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1542 j) = 396714205 := by decide
private theorem lowerTwo_row_1543 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1543 j) = 396652192 := by decide
private theorem lowerTwo_row_1544 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1544 j) = 397478602 := by decide
private theorem lowerTwo_row_1545 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1545 j) = 398305284 := by decide
private theorem lowerTwo_row_1546 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1546 j) = 397772180 := by decide
private theorem lowerTwo_row_1547 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1547 j) = 398598412 := by decide
private theorem lowerTwo_row_1548 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1548 j) = 398492215 := by decide
private theorem lowerTwo_row_1549 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1549 j) = 399360181 := by decide
private theorem lowerTwo_row_1550 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1550 j) = 399253348 := by decide
private theorem lowerTwo_row_1551 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1551 j) = 399608288 := by decide
private theorem lowerTwo_row_1552 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1552 j) = 400476058 := by decide
private theorem lowerTwo_row_1553 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1553 j) = 400367719 := by decide
private theorem lowerTwo_row_1554 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1554 j) = 401193334 := by decide
private theorem lowerTwo_row_1555 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1555 j) = 401126232 := by decide
private theorem lowerTwo_row_1556 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1556 j) = 401479847 := by decide
private theorem lowerTwo_row_1557 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1557 j) = 401369822 := by decide
private theorem lowerTwo_row_1558 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1558 j) = 402236680 := by decide
private theorem lowerTwo_row_1559 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1559 j) = 403061937 := by decide
private theorem lowerTwo_row_1560 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1560 j) = 402950731 := by decide
private theorem lowerTwo_row_1561 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1561 j) = 403344886 := by decide
private theorem lowerTwo_row_1562 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1562 j) = 403232688 := by decide
private theorem lowerTwo_row_1563 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1563 j) = 404057259 := by decide
private theorem lowerTwo_row_1564 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1564 j) = 403986193 := by decide
private theorem lowerTwo_row_1565 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1565 j) = 404810598 := by decide
private theorem lowerTwo_row_1566 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1566 j) = 405161530 := by decide
private theorem lowerTwo_row_1567 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1567 j) = 405088950 := by decide
private theorem lowerTwo_row_1568 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1568 j) = 405913181 := by decide
private theorem lowerTwo_row_1569 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1569 j) = 405798039 := by decide
private theorem lowerTwo_row_1570 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1570 j) = 406663889 := by decide
private theorem lowerTwo_row_1571 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1571 j) = 406073340 := by decide
private theorem lowerTwo_row_1572 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1572 j) = 406896842 := by decide
private theorem lowerTwo_row_1573 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1573 j) = 407762510 := by decide
private theorem lowerTwo_row_1574 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1574 j) = 407645194 := by decide
private theorem lowerTwo_row_1575 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1575 j) = 408468784 := by decide
private theorem lowerTwo_row_1576 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1576 j) = 407916855 := by decide
private theorem lowerTwo_row_1577 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1577 j) = 408740026 := by decide
private theorem lowerTwo_row_1578 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1578 j) = 408620941 := by decide
private theorem lowerTwo_row_1579 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1579 j) = 409485726 := by decide
private theorem lowerTwo_row_1580 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1580 j) = 410309008 := by decide
private theorem lowerTwo_row_1581 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1581 j) = 409711975 := by decide
private theorem lowerTwo_row_1582 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1582 j) = 410576584 := by decide
private theorem lowerTwo_row_1583 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1583 j) = 410455294 := by decide
private theorem lowerTwo_row_1584 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1584 j) = 411277858 := by decide
private theorem lowerTwo_row_1585 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1585 j) = 411197662 := by decide
private theorem lowerTwo_row_1586 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1586 j) = 411542313 := by decide
private theorem lowerTwo_row_1587 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1587 j) = 412364739 := by decide
private theorem lowerTwo_row_1588 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1588 j) = 412282991 := by decide
private theorem lowerTwo_row_1589 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1589 j) = 413105208 := by decide
private theorem lowerTwo_row_1590 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1590 j) = 412980955 := by decide
private theorem lowerTwo_row_1591 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1591 j) = 413366018 := by decide
private theorem lowerTwo_row_1592 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1592 j) = 413240735 := by decide
private theorem lowerTwo_row_1593 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1593 j) = 414062280 := by decide
private theorem lowerTwo_row_1594 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1594 j) = 414925909 := by decide
private theorem lowerTwo_row_1595 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1595 j) = 414799389 := by decide
private theorem lowerTwo_row_1596 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1596 j) = 415141311 := by decide
private theorem lowerTwo_row_1597 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1597 j) = 415055518 := by decide
private theorem lowerTwo_row_1598 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1598 j) = 415876692 := by decide
private theorem lowerTwo_row_1599 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1599 j) = 415748441 := by decide
private theorem lowerTwo_row_1600 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1600 j) = 416611169 := by decide
private theorem lowerTwo_row_1601 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1601 j) = 416951678 := by decide
private theorem lowerTwo_row_1602 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1602 j) = 416821876 := by decide
private theorem lowerTwo_row_1603 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1603 j) = 417684407 := by decide
private theorem lowerTwo_row_1604 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1604 j) = 417553901 := by decide
private theorem lowerTwo_row_1605 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1605 j) = 418374516 := by decide
private theorem lowerTwo_row_1606 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1606 j) = 417803145 := by decide
private theorem lowerTwo_row_1607 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1607 j) = 418623288 := by decide
private theorem lowerTwo_row_1608 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1608 j) = 419443724 := by decide
private theorem lowerTwo_row_1609 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1609 j) = 419352602 := by decide
private theorem lowerTwo_row_1610 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1610 j) = 420172891 := by decide
private theorem lowerTwo_row_1611 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1611 j) = 419556459 := by decide
private theorem lowerTwo_row_1612 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1612 j) = 420417939 := by decide
private theorem lowerTwo_row_1613 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1613 j) = 420283378 := by decide
private theorem lowerTwo_row_1614 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1614 j) = 421102920 := by decide
private theorem lowerTwo_row_1615 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1615 j) = 421964512 := by decide
private theorem lowerTwo_row_1616 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1616 j) = 421344764 := by decide
private theorem lowerTwo_row_1617 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1617 j) = 422164139 := by decide
private theorem lowerTwo_row_1618 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1618 j) = 422068946 := by decide
private theorem lowerTwo_row_1619 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1619 j) = 422888166 := by decide
private theorem lowerTwo_row_1620 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1620 j) = 422750497 := by decide
private theorem lowerTwo_row_1621 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1621 j) = 423126266 := by decide
private theorem lowerTwo_row_1622 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1622 j) = 423945299 := by decide
private theorem lowerTwo_row_1623 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1623 j) = 423806092 := by decide
private theorem lowerTwo_row_1624 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1624 j) = 424666618 := by decide
private theorem lowerTwo_row_1625 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1625 j) = 424526636 := by decide
private theorem lowerTwo_row_1626 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1626 j) = 424859276 := by decide
private theorem lowerTwo_row_1627 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1627 j) = 424759929 := by decide
private theorem lowerTwo_row_1628 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1628 j) = 425578066 := by decide
private theorem lowerTwo_row_1629 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1629 j) = 426396603 := by decide
private theorem lowerTwo_row_1630 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1630 j) = 426295936 := by decide
private theorem lowerTwo_row_1631 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1631 j) = 426627171 := by decide
private theorem lowerTwo_row_1632 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1632 j) = 426483805 := by decide
private theorem lowerTwo_row_1633 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1633 j) = 427343256 := by decide
private theorem lowerTwo_row_1634 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1634 j) = 427199127 := by decide
private theorem lowerTwo_row_1635 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1635 j) = 428016739 := by decide
private theorem lowerTwo_row_1636 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1636 j) = 428388175 := by decide
private theorem lowerTwo_row_1637 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1637 j) = 428242458 := by decide
private theorem lowerTwo_row_1638 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1638 j) = 429059921 := by decide
private theorem lowerTwo_row_1639 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1639 j) = 428955032 := by decide
private theorem lowerTwo_row_1640 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1640 j) = 429772312 := by decide
private theorem lowerTwo_row_1641 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1641 j) = 429135850 := by decide
private theorem lowerTwo_row_1642 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1642 j) = 429994190 := by decide
private theorem lowerTwo_row_1643 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1643 j) = 430811319 := by decide
private theorem lowerTwo_row_1644 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1644 j) = 430662454 := by decide
private theorem lowerTwo_row_1645 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1645 j) = 431520943 := by decide
private theorem lowerTwo_row_1646 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1646 j) = 430881042 := by decide
private theorem lowerTwo_row_1647 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1647 j) = 431697432 := by decide
private theorem lowerTwo_row_1648 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1648 j) = 431588324 := by decide
private theorem lowerTwo_row_1649 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1649 j) = 432404544 := by decide
private theorem lowerTwo_row_1650 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1650 j) = 433221074 := by decide
private theorem lowerTwo_row_1651 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1651 j) = 432619242 := by decide
private theorem lowerTwo_row_1652 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1652 j) = 433435313 := by decide
private theorem lowerTwo_row_1653 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1653 j) = 433282162 := by decide
private theorem lowerTwo_row_1654 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1654 j) = 434139581 := by decide
private theorem lowerTwo_row_1655 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1655 j) = 433985673 := by decide
private theorem lowerTwo_row_1656 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1656 j) = 434308830 := by decide
private theorem lowerTwo_row_1657 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1657 j) = 435166044 := by decide
private theorem lowerTwo_row_1658 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1658 j) = 435010488 := by decide
private theorem lowerTwo_row_1659 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1659 j) = 435825913 := by decide
private theorem lowerTwo_row_1660 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1660 j) = 435711074 := by decide
private theorem lowerTwo_row_1661 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1661 j) = 436032831 := by decide
private theorem lowerTwo_row_1662 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1662 j) = 435875325 := by decide
private theorem lowerTwo_row_1663 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1663 j) = 436731577 := by decide
private theorem lowerTwo_row_1664 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1664 j) = 437546592 := by decide
private theorem lowerTwo_row_1665 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1665 j) = 437387770 := by decide
private theorem lowerTwo_row_1666 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1666 j) = 437749560 := by decide
private theorem lowerTwo_row_1667 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1667 j) = 437589608 := by decide
private theorem lowerTwo_row_1668 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1668 j) = 438403899 := by decide
private theorem lowerTwo_row_1669 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1669 j) = 438284678 := by decide
private theorem lowerTwo_row_1670 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1670 j) = 439098740 := by decide
private theorem lowerTwo_row_1671 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1671 j) = 439417574 := by decide
private theorem lowerTwo_row_1672 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1672 j) = 439296599 := by decide
private theorem lowerTwo_row_1673 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1673 j) = 440110512 := by decide
private theorem lowerTwo_row_1674 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1674 j) = 439947266 := by decide
private theorem lowerTwo_row_1675 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1675 j) = 440802411 := by decide
private theorem lowerTwo_row_1676 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1676 j) = 440141716 := by decide
private theorem lowerTwo_row_1677 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1677 j) = 440954827 := by decide
private theorem lowerTwo_row_1678 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1678 j) = 441809796 := by decide
private theorem lowerTwo_row_1679 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1679 j) = 441644071 := by decide
private theorem lowerTwo_row_1680 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1680 j) = 442457289 := by decide
private theorem lowerTwo_row_1681 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1681 j) = 441834438 := by decide
private theorem lowerTwo_row_1682 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1682 j) = 442647208 := by decide
private theorem lowerTwo_row_1683 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1683 j) = 442479485 := by decide
private theorem lowerTwo_row_1684 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1684 j) = 443333438 := by decide
private theorem lowerTwo_row_1685 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1685 j) = 444146341 := by decide
private theorem lowerTwo_row_1686 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1686 j) = 443478375 := by decide
private theorem lowerTwo_row_1687 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1687 j) = 444332188 := by decide
private theorem lowerTwo_row_1688 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1688 j) = 444161916 := by decide
private theorem lowerTwo_row_1689 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1689 j) = 444974023 := by decide
private theorem lowerTwo_row_1690 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1690 j) = 444844377 := by decide
private theorem lowerTwo_row_1691 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1691 j) = 445156373 := by decide
private theorem lowerTwo_row_1692 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1692 j) = 445968304 := by decide
private theorem lowerTwo_row_1693 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1693 j) = 445836898 := by decide
private theorem lowerTwo_row_1694 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1694 j) = 446648635 := by decide
private theorem lowerTwo_row_1695 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1695 j) = 446474954 := by decide
private theorem lowerTwo_row_1696 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1696 j) = 446826889 := by decide
private theorem lowerTwo_row_1697 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1697 j) = 446652062 := by decide
private theorem lowerTwo_row_1698 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1698 j) = 447463005 := by decide
private theorem lowerTwo_row_1699 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1699 j) = 448315717 := by decide
private theorem lowerTwo_row_1700 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1700 j) = 448139480 := by decide
private theorem lowerTwo_row_1701 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1701 j) = 448448485 := by decide
private theorem lowerTwo_row_1702 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1702 j) = 448312457 := by decide
private theorem lowerTwo_row_1703 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1703 j) = 449123015 := by decide
private theorem lowerTwo_row_1704 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1704 j) = 448944754 := by decide
private theorem lowerTwo_row_1705 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1705 j) = 449796463 := by decide
private theorem lowerTwo_row_1706 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1706 j) = 450103959 := by decide
private theorem lowerTwo_row_1707 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1707 j) = 449923946 := by decide
private theorem lowerTwo_row_1708 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1708 j) = 450775445 := by decide
private theorem lowerTwo_row_1709 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1709 j) = 450594593 := by decide
private theorem lowerTwo_row_1710 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1710 j) = 451404508 := by decide
private theorem lowerTwo_row_1711 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1711 j) = 450759819 := by decide
private theorem lowerTwo_row_1712 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1712 j) = 451569193 := by decide
private theorem lowerTwo_row_1713 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1713 j) = 452378889 := by decide
private theorem lowerTwo_row_1714 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1714 j) = 452236763 := by decide
private theorem lowerTwo_row_1715 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1715 j) = 453046257 := by decide
private theorem lowerTwo_row_1716 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1716 j) = 452356452 := by decide
private theorem lowerTwo_row_1717 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1717 j) = 453206748 := by decide
private theorem lowerTwo_row_1718 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1718 j) = 453021215 := by decide
private theorem lowerTwo_row_1719 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1719 j) = 453829896 := by decide
private theorem lowerTwo_row_1720 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1720 j) = 454680352 := by decide
private theorem lowerTwo_row_1721 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1721 j) = 453986778 := by decide
private theorem lowerTwo_row_1722 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1722 j) = 454795266 := by decide
private theorem lowerTwo_row_1723 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1723 j) = 454648416 := by decide
private theorem lowerTwo_row_1724 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1724 j) = 455456701 := by decide
private theorem lowerTwo_row_1725 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1725 j) = 455267598 := by decide
private theorem lowerTwo_row_1726 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1726 j) = 455609301 := by decide
private theorem lowerTwo_row_1727 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1727 j) = 456417409 := by decide
private theorem lowerTwo_row_1728 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1728 j) = 456226519 := by decide
private theorem lowerTwo_row_1729 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1729 j) = 457075727 := by decide
private theorem lowerTwo_row_1730 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1730 j) = 456883956 := by decide
private theorem lowerTwo_row_1731 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1731 j) = 457182734 := by decide
private theorem lowerTwo_row_1732 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1732 j) = 457031069 := by decide
private theorem lowerTwo_row_1733 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1733 j) = 457838130 := by decide
private theorem lowerTwo_row_1734 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1734 j) = 458645582 := by decide
private theorem lowerTwo_row_1735 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1735 j) = 458492424 := by decide
private theorem lowerTwo_row_1736 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1736 j) = 458789640 := by decide
private theorem lowerTwo_row_1737 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1737 j) = 458593936 := by decide
private theorem lowerTwo_row_1738 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1738 j) = 459441871 := by decide
private theorem lowerTwo_row_1739 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1739 j) = 459245276 := by decide
private theorem lowerTwo_row_1740 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1740 j) = 460051696 := by decide
private theorem lowerTwo_row_1741 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1741 j) = 460388559 := by decide
private theorem lowerTwo_row_1742 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1742 j) = 460190184 := by decide
private theorem lowerTwo_row_1743 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1743 j) = 460996384 := by decide
private theorem lowerTwo_row_1744 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1744 j) = 460838320 := by decide
private theorem lowerTwo_row_1745 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1745 j) = 461644333 := by decide
private theorem lowerTwo_row_1746 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1746 j) = 460931778 := by decide
private theorem lowerTwo_row_1747 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1747 j) = 461778419 := by decide
private theorem lowerTwo_row_1748 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1748 j) = 462584199 := by decide
private theorem lowerTwo_row_1749 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1749 j) = 462382114 := by decide
private theorem lowerTwo_row_1750 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1750 j) = 463228916 := by decide
private theorem lowerTwo_row_1751 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1751 j) = 462512465 := by decide
private theorem lowerTwo_row_1752 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1752 j) = 463317376 := by decide
private theorem lowerTwo_row_1753 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1753 j) = 463154429 := by decide
private theorem lowerTwo_row_1754 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1754 j) = 463959118 := by decide
private theorem lowerTwo_row_1755 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1755 j) = 464764193 := by decide
private theorem lowerTwo_row_1756 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1756 j) = 464085010 := by decide
private theorem lowerTwo_row_1757 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1757 j) = 464889506 := by decide
private theorem lowerTwo_row_1758 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1758 j) = 464682471 := by decide
private theorem lowerTwo_row_1759 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1759 j) = 465527992 := by decide
private theorem lowerTwo_row_1760 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1760 j) = 465320056 := by decide
private theorem lowerTwo_row_1761 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1761 j) = 465608162 := by decide
private theorem lowerTwo_row_1762 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1762 j) = 466453456 := by decide
private theorem lowerTwo_row_1763 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1763 j) = 466243637 := by decide
private theorem lowerTwo_row_1764 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1764 j) = 467047425 := by decide
private theorem lowerTwo_row_1765 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1765 j) = 466877917 := by decide
private theorem lowerTwo_row_1766 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1766 j) = 467164382 := by decide
private theorem lowerTwo_row_1767 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1767 j) = 466952370 := by decide
private theorem lowerTwo_row_1768 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1768 j) = 467796545 := by decide
private theorem lowerTwo_row_1769 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1769 j) = 468599847 := by decide
private theorem lowerTwo_row_1770 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1770 j) = 468386296 := by decide
private theorem lowerTwo_row_1771 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1771 j) = 468712289 := by decide
private theorem lowerTwo_row_1772 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1772 j) = 468497433 := by decide
private theorem lowerTwo_row_1773 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1773 j) = 469299916 := by decide
private theorem lowerTwo_row_1774 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1774 j) = 469125307 := by decide
private theorem lowerTwo_row_1775 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1775 j) = 469927552 := by decide
private theorem lowerTwo_row_1776 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1776 j) = 470210678 := by decide
private theorem lowerTwo_row_1777 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1777 j) = 470034123 := by decide
private theorem lowerTwo_row_1778 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1778 j) = 470836143 := by decide
private theorem lowerTwo_row_1779 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1779 j) = 470617475 := by decide
private theorem lowerTwo_row_1780 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1780 j) = 471460407 := by decide
private theorem lowerTwo_row_1781 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1781 j) = 470720061 := by decide
private theorem lowerTwo_row_1782 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1782 j) = 471521210 := by decide
private theorem lowerTwo_row_1783 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1783 j) = 472363935 := by decide
private theorem lowerTwo_row_1784 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1784 j) = 472142367 := by decide
private theorem lowerTwo_row_1785 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1785 j) = 472943634 := by decide
private theorem lowerTwo_row_1786 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1786 j) = 472240325 := by decide
private theorem lowerTwo_row_1787 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1787 j) = 473041015 := by decide
private theorem lowerTwo_row_1788 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1788 j) = 472817144 := by decide
private theorem lowerTwo_row_1789 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1789 j) = 473658750 := by decide
private theorem lowerTwo_row_1790 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1790 j) = 474459524 := by decide
private theorem lowerTwo_row_1791 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1791 j) = 473710840 := by decide
private theorem lowerTwo_row_1792 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1792 j) = 474552217 := by decide
private theorem lowerTwo_row_1793 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1793 j) = 474325411 := by decide
private theorem lowerTwo_row_1794 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1794 j) = 475125327 := by decide
private theorem lowerTwo_row_1795 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1795 j) = 474938724 := by decide
private theorem lowerTwo_row_1796 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1796 j) = 475213956 := by decide
private theorem lowerTwo_row_1797 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1797 j) = 476013618 := by decide
private theorem lowerTwo_row_1798 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1798 j) = 475825026 := by decide
private theorem lowerTwo_row_1799 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1799 j) = 476624448 := by decide
private theorem lowerTwo_row_1800 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1800 j) = 476393725 := by decide
private theorem lowerTwo_row_1801 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1801 j) = 476708317 := by decide
private theorem lowerTwo_row_1802 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1802 j) = 476476202 := by decide
private theorem lowerTwo_row_1803 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1803 j) = 477274716 := by decide
private theorem lowerTwo_row_1804 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1804 j) = 478114675 := by decide
private theorem lowerTwo_row_1805 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1805 j) = 477880908 := by decide
private theorem lowerTwo_row_1806 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1806 j) = 478152614 := by decide
private theorem lowerTwo_row_1807 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1807 j) = 477958575 := by decide
private theorem lowerTwo_row_1808 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1808 j) = 478756499 := by decide
private theorem lowerTwo_row_1809 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1809 j) = 478520271 := by decide
private theorem lowerTwo_row_1810 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1810 j) = 479358970 := by decide
private theorem lowerTwo_row_1811 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1811 j) = 479628947 := by decide
private theorem lowerTwo_row_1812 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1812 j) = 479390682 := by decide
private theorem lowerTwo_row_1813 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1813 j) = 480229092 := by decide
private theorem lowerTwo_row_1814 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1814 j) = 479989807 := by decide
private theorem lowerTwo_row_1815 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1815 j) = 480786811 := by decide
private theorem lowerTwo_row_1816 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1816 j) = 480058359 := by decide
private theorem lowerTwo_row_1817 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1817 j) = 480854743 := by decide
private theorem lowerTwo_row_1818 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1818 j) = 481651450 := by decide
private theorem lowerTwo_row_1819 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1819 j) = 481450104 := by decide
private theorem lowerTwo_row_1820 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1820 j) = 482246540 := by decide
private theorem lowerTwo_row_1821 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1821 j) = 481472643 := by decide
private theorem lowerTwo_row_1822 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1822 j) = 482309487 := by decide
private theorem lowerTwo_row_1823 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1823 j) = 482064582 := by decide
private theorem lowerTwo_row_1824 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1824 j) = 482860012 := by decide
private theorem lowerTwo_row_1825 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1825 j) = 483696907 := by decide
private theorem lowerTwo_row_1826 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1826 j) = 482918658 := by decide
private theorem lowerTwo_row_1827 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1827 j) = 483713791 := by decide
private theorem lowerTwo_row_1828 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1828 j) = 483506814 := by decide
private theorem lowerTwo_row_1829 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1829 j) = 484301625 := by decide
private theorem lowerTwo_row_1830 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1830 j) = 484052474 := by decide
private theorem lowerTwo_row_1831 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1831 j) = 484355240 := by decide
private theorem lowerTwo_row_1832 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1832 j) = 485149744 := by decide
private theorem lowerTwo_row_1833 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1833 j) = 484898481 := by decide
private theorem lowerTwo_row_1834 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1834 j) = 485733748 := by decide
private theorem lowerTwo_row_1835 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1835 j) = 485481390 := by decide
private theorem lowerTwo_row_1836 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1836 j) = 485741232 := by decide
private theorem lowerTwo_row_1837 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1837 j) = 485528523 := by decide
private theorem lowerTwo_row_1838 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1838 j) = 486321708 := by decide
private theorem lowerTwo_row_1839 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1839 j) = 487115238 := by decide
private theorem lowerTwo_row_1840 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1840 j) = 486900712 := by decide
private theorem lowerTwo_row_1841 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1841 j) = 487158674 := by decide
private theorem lowerTwo_row_1842 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1842 j) = 486901664 := by decide
private theorem lowerTwo_row_1843 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1843 j) = 487735228 := by decide
private theorem lowerTwo_row_1844 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1844 j) = 487477137 := by decide
private theorem lowerTwo_row_1845 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1845 j) = 488269295 := by decide
private theorem lowerTwo_row_1846 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1846 j) = 488566437 := by decide
private theorem lowerTwo_row_1847 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1847 j) = 488306153 := by decide
private theorem lowerTwo_row_1848 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1848 j) = 489098032 := by decide
private theorem lowerTwo_row_1849 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1849 j) = 488877632 := by decide
private theorem lowerTwo_row_1850 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1850 j) = 489669173 := by decide
private theorem lowerTwo_row_1851 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1851 j) = 488868957 := by decide
private theorem lowerTwo_row_1852 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1852 j) = 489700795 := by decide
private theorem lowerTwo_row_1853 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1853 j) = 490492032 := by decide
private theorem lowerTwo_row_1854 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1854 j) = 490227301 := by decide
private theorem lowerTwo_row_1855 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1855 j) = 491059165 := by decide
private theorem lowerTwo_row_1856 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1856 j) = 490254393 := by decide
private theorem lowerTwo_row_1857 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1857 j) = 491044512 := by decide
private theorem lowerTwo_row_1858 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1858 j) = 490818218 := by decide
private theorem lowerTwo_row_1859 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1859 j) = 491608043 := by decide
private theorem lowerTwo_row_1860 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1860 j) = 492398190 := by decide
private theorem lowerTwo_row_1861 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1861 j) = 491629813 := by decide
private theorem lowerTwo_row_1862 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1862 j) = 492419279 := by decide
private theorem lowerTwo_row_1863 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1863 j) = 492148564 := by decide
private theorem lowerTwo_row_1864 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1864 j) = 492978709 := by decide
private theorem lowerTwo_row_1865 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1865 j) = 492706890 := by decide
private theorem lowerTwo_row_1866 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1866 j) = 492954132 := by decide
private theorem lowerTwo_row_1867 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1867 j) = 493783923 := by decide
private theorem lowerTwo_row_1868 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1868 j) = 493509823 := by decide
private theorem lowerTwo_row_1869 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1869 j) = 494298256 := by decide
private theorem lowerTwo_row_1870 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1870 j) = 494063998 := by decide
private theorem lowerTwo_row_1871 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1871 j) = 494309309 := by decide
private theorem lowerTwo_row_1872 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1872 j) = 494032557 := by decide
private theorem lowerTwo_row_1873 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1873 j) = 494860852 := by decide
private theorem lowerTwo_row_1874 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1874 j) = 495648555 := by decide
private theorem lowerTwo_row_1875 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1875 j) = 495369885 := by decide
private theorem lowerTwo_row_1876 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1876 j) = 495654148 := by decide
private theorem lowerTwo_row_1877 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1877 j) = 495373962 := by decide
private theorem lowerTwo_row_1878 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1878 j) = 496160546 := by decide
private theorem lowerTwo_row_1879 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1879 j) = 495920126 := by decide
private theorem lowerTwo_row_1880 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1880 j) = 496706372 := by decide
private theorem lowerTwo_row_1881 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1881 j) = 496947649 := by decide
private theorem lowerTwo_row_1882 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1882 j) = 496704922 := by decide
private theorem lowerTwo_row_1883 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1883 j) = 497490817 := by decide
private theorem lowerTwo_row_1884 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1884 j) = 497205919 := by decide
private theorem lowerTwo_row_1885 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1885 j) = 498032353 := by decide
private theorem lowerTwo_row_1886 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1886 j) = 497199694 := by decide
private theorem lowerTwo_row_1887 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1887 j) = 497984443 := by decide
private theorem lowerTwo_row_1888 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1888 j) = 498810484 := by decide
private theorem lowerTwo_row_1889 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1889 j) = 498522113 := by decide
private theorem lowerTwo_row_1890 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1890 j) = 499306845 := by decide
private theorem lowerTwo_row_1891 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1891 j) = 498510267 := by decide
private theorem lowerTwo_row_1892 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1892 j) = 499294242 := by decide
private theorem lowerTwo_row_1893 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1893 j) = 499003081 := by decide
private theorem lowerTwo_row_1894 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1894 j) = 499827596 := by decide
private theorem lowerTwo_row_1895 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1895 j) = 500273997 := by decide
private theorem lowerTwo_row_1896 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1896 j) = 499093810 := by decide
private theorem lowerTwo_row_1897 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1897 j) = 499241547 := by decide
private theorem lowerTwo_row_1898 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1898 j) = 498608564 := by decide
private theorem lowerTwo_row_1899 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1899 j) = 499053012 := by decide
private theorem lowerTwo_row_1900 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1900 j) = 498119666 := by decide
private theorem lowerTwo_row_1901 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1901 j) = 498012639 := by decide
private theorem lowerTwo_row_1902 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1902 j) = 498456058 := by decide
private theorem lowerTwo_row_1903 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1903 j) = 497518466 := by decide
private theorem lowerTwo_row_1904 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1904 j) = 497960962 := by decide
private theorem lowerTwo_row_1905 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1905 j) = 497321730 := by decide
private theorem lowerTwo_row_1906 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1906 j) = 496910279 := by decide
private theorem lowerTwo_row_1907 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1907 j) = 496268911 := by decide
private theorem lowerTwo_row_1908 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1908 j) = 496709446 := by decide
private theorem lowerTwo_row_1909 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1909 j) = 496847601 := by decide
private theorem lowerTwo_row_1910 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1910 j) = 496203528 := by decide
private theorem lowerTwo_row_1911 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1911 j) = 496090153 := by decide
private theorem lowerTwo_row_1912 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1912 j) = 495140266 := by decide
private theorem lowerTwo_row_1913 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1913 j) = 495578822 := by decide
private theorem lowerTwo_row_1914 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1914 j) = 494931095 := by decide
private theorem lowerTwo_row_1915 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1915 j) = 495063738 := by decide
private theorem lowerTwo_row_1916 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1916 j) = 494946987 := by decide
private theorem lowerTwo_row_1917 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1917 j) = 494296132 := by decide
private theorem lowerTwo_row_1918 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1918 j) = 494426421 := by decide
private theorem lowerTwo_row_1919 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1919 j) = 493773789 := by decide
private theorem lowerTwo_row_1920 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1920 j) = 494209608 := by decide
private theorem lowerTwo_row_1921 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1921 j) = 492691658 := by decide
private theorem lowerTwo_row_1922 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1922 j) = 493126140 := by decide
private theorem lowerTwo_row_1923 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1923 j) = 493560853 := by decide
private theorem lowerTwo_row_1924 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1924 j) = 492594420 := by decide
private theorem lowerTwo_row_1925 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1925 j) = 493028182 := by decide
private theorem lowerTwo_row_1926 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1926 j) = 491811664 := by decide
private theorem lowerTwo_row_1927 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1927 j) = 491933933 := by decide
private theorem lowerTwo_row_1928 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1928 j) = 491272511 := by decide
private theorem lowerTwo_row_1929 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1929 j) = 491704167 := by decide
private theorem lowerTwo_row_1930 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1930 j) = 491824434 := by decide
private theorem lowerTwo_row_1931 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1931 j) = 490601464 := by decide
private theorem lowerTwo_row_1932 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1932 j) = 491031978 := by decide
private theorem lowerTwo_row_1933 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1933 j) = 490052806 := by decide
private theorem lowerTwo_row_1934 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1934 j) = 490482323 := by decide
private theorem lowerTwo_row_1935 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1935 j) = 489814243 := by decide
private theorem lowerTwo_row_1936 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1936 j) = 489368629 := by decide
private theorem lowerTwo_row_1937 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1937 j) = 489796980 := by decide
private theorem lowerTwo_row_1938 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1938 j) = 489125687 := by decide
private theorem lowerTwo_row_1939 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1939 j) = 489237675 := by decide
private theorem lowerTwo_row_1940 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1940 j) = 488564455 := by decide
private theorem lowerTwo_row_1941 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1941 j) = 488429591 := by decide
private theorem lowerTwo_row_1942 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1942 j) = 487437442 := by decide
private theorem lowerTwo_row_1943 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1943 j) = 487862643 := by decide
private theorem lowerTwo_row_1944 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1944 j) = 488288147 := by decide
private theorem lowerTwo_row_1945 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1945 j) = 487291928 := by decide
private theorem lowerTwo_row_1946 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1946 j) = 487153511 := by decide
private theorem lowerTwo_row_1947 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1947 j) = 486473214 := by decide
private theorem lowerTwo_row_1948 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1948 j) = 486577165 := by decide
private theorem lowerTwo_row_1949 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1949 j) = 485894974 := by decide
private theorem lowerTwo_row_1950 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1950 j) = 486317331 := by decide
private theorem lowerTwo_row_1951 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1951 j) = 485854943 := by decide
private theorem lowerTwo_row_1952 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1952 j) = 485169498 := by decide
private theorem lowerTwo_row_1953 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1953 j) = 485590693 := by decide
private theorem lowerTwo_row_1954 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1954 j) = 484581651 := by decide
private theorem lowerTwo_row_1955 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1955 j) = 485001857 := by decide
private theorem lowerTwo_row_1956 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1956 j) = 483747114 := by decide
private theorem lowerTwo_row_1957 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1957 j) = 483842897 := by decide
private theorem lowerTwo_row_1958 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1958 j) = 484261966 := by decide
private theorem lowerTwo_row_1959 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1959 j) = 483569630 := by decide
private theorem lowerTwo_row_1960 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1960 j) = 483663359 := by decide
private theorem lowerTwo_row_1961 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1961 j) = 482401927 := by decide
private theorem lowerTwo_row_1962 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1962 j) = 482818752 := by decide
private theorem lowerTwo_row_1963 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1963 j) = 481796642 := by decide
private theorem lowerTwo_row_1964 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1964 j) = 482212428 := by decide
private theorem lowerTwo_row_1965 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1965 j) = 482628434 := by decide
private theorem lowerTwo_row_1966 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1966 j) = 481033450 := by decide
private theorem lowerTwo_row_1967 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1967 j) = 481448014 := by decide
private theorem lowerTwo_row_1968 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1968 j) = 480746306 := by decide
private theorem lowerTwo_row_1969 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1969 j) = 480831752 := by decide
private theorem lowerTwo_row_1970 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1970 j) = 480128078 := by decide
private theorem lowerTwo_row_1971 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1971 j) = 479970723 := by decide
private theorem lowerTwo_row_1972 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1972 j) = 480053597 := by decide
private theorem lowerTwo_row_1973 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1973 j) = 479346517 := by decide
private theorem lowerTwo_row_1974 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1974 j) = 479757980 := by decide
private theorem lowerTwo_row_1975 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1975 j) = 478718212 := by decide
private theorem lowerTwo_row_1976 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1976 j) = 478557042 := by decide
private theorem lowerTwo_row_1977 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1977 j) = 477845836 := by decide
private theorem lowerTwo_row_1978 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1978 j) = 477922730 := by decide
private theorem lowerTwo_row_1979 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1979 j) = 478331808 := by decide
private theorem lowerTwo_row_1980 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1980 j) = 477617552 := by decide
private theorem lowerTwo_row_1981 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1981 j) = 477119218 := by decide
private theorem lowerTwo_row_1982 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1982 j) = 476402499 := by decide
private theorem lowerTwo_row_1983 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1983 j) = 476809280 := by decide
private theorem lowerTwo_row_1984 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1984 j) = 475755879 := by decide
private theorem lowerTwo_row_1985 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1985 j) = 476161545 := by decide
private theorem lowerTwo_row_1986 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1986 j) = 475992920 := by decide
private theorem lowerTwo_row_1987 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1987 j) = 474934643 := by decide
private theorem lowerTwo_row_1988 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1988 j) = 475338993 := by decide
private theorem lowerTwo_row_1989 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1989 j) = 474614945 := by decide
private theorem lowerTwo_row_1990 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1990 j) = 474680841 := by decide
private theorem lowerTwo_row_1991 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1991 j) = 473378717 := by decide
private theorem lowerTwo_row_1992 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1992 j) = 473780646 := by decide
private theorem lowerTwo_row_1993 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1993 j) = 473843834 := by decide
private theorem lowerTwo_row_1994 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1994 j) = 473114185 := by decide
private theorem lowerTwo_row_1995 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1995 j) = 473515178 := by decide
private theorem lowerTwo_row_1996 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1996 j) = 471865842 := by decide
private theorem lowerTwo_row_1997 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1997 j) = 472265298 := by decide
private theorem lowerTwo_row_1998 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1998 j) = 471531238 := by decide
private theorem lowerTwo_row_1999 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1999 j) = 471588199 := by decide
private theorem lowerTwo_row_2000 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2000 j) = 471986727 := by decide
private theorem lowerTwo_row_2001 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2001 j) = 470670437 := by decide
private theorem lowerTwo_row_2002 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2002 j) = 470724630 := by decide
private theorem lowerTwo_row_2003 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2003 j) = 469984848 := by decide
private theorem lowerTwo_row_2004 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2004 j) = 470380871 := by decide
private theorem lowerTwo_row_2005 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2005 j) = 469294845 := by decide
private theorem lowerTwo_row_2006 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2006 j) = 469109180 := by decide
private theorem lowerTwo_row_2007 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2007 j) = 469503801 := by decide
private theorem lowerTwo_row_2008 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2008 j) = 468412733 := by decide
private theorem lowerTwo_row_2009 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2009 j) = 468806185 := by decide
private theorem lowerTwo_row_2010 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2010 j) = 468058705 := by decide
private theorem lowerTwo_row_2011 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2011 j) = 467522045 := by decide
private theorem lowerTwo_row_2012 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2012 j) = 466771959 := by decide
private theorem lowerTwo_row_2013 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2013 j) = 467162888 := by decide
private theorem lowerTwo_row_2014 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2014 j) = 467205473 := by decide
private theorem lowerTwo_row_2015 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2015 j) = 466452140 := by decide
private theorem lowerTwo_row_2016 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2016 j) = 466258468 := by decide
private theorem lowerTwo_row_2017 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2017 j) = 465152980 := by decide
private theorem lowerTwo_row_2018 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2018 j) = 465541295 := by decide
private theorem lowerTwo_row_2019 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2019 j) = 464783509 := by decide
private theorem lowerTwo_row_2020 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2020 j) = 464819770 := by decide
private theorem lowerTwo_row_2021 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2021 j) = 464621973 := by decide
private theorem lowerTwo_row_2022 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2022 j) = 463860456 := by decide
private theorem lowerTwo_row_2023 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2023 j) = 463893932 := by decide
private theorem lowerTwo_row_2024 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2024 j) = 463130262 := by decide
private theorem lowerTwo_row_2025 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2025 j) = 463515043 := by decide
private theorem lowerTwo_row_2026 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2026 j) = 461808855 := by decide
private theorem lowerTwo_row_2027 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2027 j) = 462192030 := by decide
private theorem lowerTwo_row_2028 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2028 j) = 462575395 := by decide
private theorem lowerTwo_row_2029 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2029 j) = 461450814 := by decide
private theorem lowerTwo_row_2030 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2030 j) = 461832960 := by decide
private theorem lowerTwo_row_2031 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2031 j) = 460472978 := by decide
private theorem lowerTwo_row_2032 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2032 j) = 460497252 := by decide
private theorem lowerTwo_row_2033 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2033 j) = 459722951 := by decide
private theorem lowerTwo_row_2034 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2034 j) = 460102413 := by decide
private theorem lowerTwo_row_2035 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2035 j) = 460124311 := by decide
private theorem lowerTwo_row_2036 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2036 j) = 458756682 := by decide
private theorem lowerTwo_row_2037 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2037 j) = 459134680 := by decide
private theorem lowerTwo_row_2038 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2038 j) = 457995355 := by decide
private theorem lowerTwo_row_2039 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2039 j) = 458372108 := by decide
private theorem lowerTwo_row_2040 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2040 j) = 457589681 := by decide
private theorem lowerTwo_row_2041 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2041 j) = 457013392 := by decide
private theorem lowerTwo_row_2042 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2042 j) = 457388613 := by decide
private theorem lowerTwo_row_2043 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2043 j) = 456602311 := by decide
private theorem lowerTwo_row_2044 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2044 j) = 456614595 := by decide
private theorem lowerTwo_row_2045 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2045 j) = 455825976 := by decide
private theorem lowerTwo_row_2046 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2046 j) = 455605857 := by decide
private theorem lowerTwo_row_2047 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2047 j) = 454451439 := by decide
private theorem lowerTwo_row_2048 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2048 j) = 453659220 := by decide
private theorem lowerTwo_row_2049 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2049 j) = 452866151 := by decide
private theorem lowerTwo_row_2050 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2050 j) = 452870267 := by decide
private theorem lowerTwo_row_2051 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2051 j) = 452644239 := by decide
private theorem lowerTwo_row_2052 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2052 j) = 453012658 := by decide
private theorem lowerTwo_row_2053 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2053 j) = 453015166 := by decide
private theorem lowerTwo_row_2054 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2054 j) = 453383658 := by decide
private theorem lowerTwo_row_2055 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2055 j) = 453752305 := by decide
private theorem lowerTwo_row_2056 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2056 j) = 453157266 := by decide
private theorem lowerTwo_row_2057 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2057 j) = 453525540 := by decide
private theorem lowerTwo_row_2058 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2058 j) = 453893956 := by decide
private theorem lowerTwo_row_2059 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2059 j) = 453893610 := by decide
private theorem lowerTwo_row_2060 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2060 j) = 454262118 := by decide
private theorem lowerTwo_row_2061 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2061 j) = 454032758 := by decide
private theorem lowerTwo_row_2062 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2062 j) = 454030787 := by decide
private theorem lowerTwo_row_2063 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2063 j) = 454399054 := by decide
private theorem lowerTwo_row_2064 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2064 j) = 454767431 := by decide
private theorem lowerTwo_row_2065 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2065 j) = 454764275 := by decide
private theorem lowerTwo_row_2066 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2066 j) = 454533146 := by decide
private theorem lowerTwo_row_2067 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2067 j) = 454901295 := by decide
private theorem lowerTwo_row_2068 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2068 j) = 454896479 := by decide
private theorem lowerTwo_row_2069 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2069 j) = 455264716 := by decide
private theorem lowerTwo_row_2070 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2070 j) = 455633100 := by decide
private theorem lowerTwo_row_2071 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2071 j) = 455025781 := by decide
private theorem lowerTwo_row_2072 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2072 j) = 455393783 := by decide
private theorem lowerTwo_row_2073 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2073 j) = 455761926 := by decide
private theorem lowerTwo_row_2074 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2074 j) = 455754227 := by decide
private theorem lowerTwo_row_2075 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2075 j) = 456122454 := by decide
private theorem lowerTwo_row_2076 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2076 j) = 455887840 := by decide
private theorem lowerTwo_row_2077 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2077 j) = 455878425 := by decide
private theorem lowerTwo_row_2078 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2078 j) = 456246411 := by decide
private theorem lowerTwo_row_2079 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2079 j) = 456614566 := by decide
private theorem lowerTwo_row_2080 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2080 j) = 456603909 := by decide
private theorem lowerTwo_row_2081 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2081 j) = 456367447 := by decide
private theorem lowerTwo_row_2082 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2082 j) = 456735424 := by decide
private theorem lowerTwo_row_2083 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2083 j) = 456723143 := by decide
private theorem lowerTwo_row_2084 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2084 j) = 457091136 := by decide
private theorem lowerTwo_row_2085 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2085 j) = 457459391 := by decide
private theorem lowerTwo_row_2086 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2086 j) = 456839649 := by decide
private theorem lowerTwo_row_2087 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2087 j) = 457207465 := by decide
private theorem lowerTwo_row_2088 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2088 j) = 457575516 := by decide
private theorem lowerTwo_row_2089 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2089 j) = 457560536 := by decide
private theorem lowerTwo_row_2090 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2090 j) = 457928688 := by decide
private theorem lowerTwo_row_2091 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2091 j) = 457688921 := by decide
private theorem lowerTwo_row_2092 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2092 j) = 457672329 := by decide
private theorem lowerTwo_row_2093 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2093 j) = 458040290 := by decide
private theorem lowerTwo_row_2094 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2094 j) = 458408384 := by decide
private theorem lowerTwo_row_2095 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2095 j) = 458390667 := by decide
private theorem lowerTwo_row_2096 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2096 j) = 458149120 := by decide
private theorem lowerTwo_row_2097 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2097 j) = 458517042 := by decide
private theorem lowerTwo_row_2098 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2098 j) = 458497705 := by decide
private theorem lowerTwo_row_2099 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2099 j) = 458865749 := by decide
private theorem lowerTwo_row_2100 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2100 j) = 459233939 := by decide
private theorem lowerTwo_row_2101 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2101 j) = 458601951 := by decide
private theorem lowerTwo_row_2102 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2102 j) = 458969776 := by decide
private theorem lowerTwo_row_2103 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2103 j) = 459337787 := by decide
private theorem lowerTwo_row_2104 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2104 j) = 459315698 := by decide
private theorem lowerTwo_row_2105 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2105 j) = 459683792 := by decide
private theorem lowerTwo_row_2106 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2106 j) = 459438798 := by decide
private theorem lowerTwo_row_2107 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2107 j) = 459415076 := by decide
private theorem lowerTwo_row_2108 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2108 j) = 459782966 := by decide
private theorem lowerTwo_row_2109 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2109 j) = 460151042 := by decide
private theorem lowerTwo_row_2110 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2110 j) = 460126130 := by decide
private theorem lowerTwo_row_2111 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2111 j) = 459879269 := by decide
private theorem lowerTwo_row_2112 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2112 j) = 460247154 := by decide
private theorem lowerTwo_row_2113 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2113 j) = 460179906 := by decide
private theorem lowerTwo_row_2114 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2114 j) = 460547839 := by decide
private theorem lowerTwo_row_2115 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2115 j) = 460915956 := by decide
private theorem lowerTwo_row_2116 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2116 j) = 460230671 := by decide
private theorem lowerTwo_row_2117 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2117 j) = 460598335 := by decide
private theorem lowerTwo_row_2118 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2118 j) = 460966190 := by decide
private theorem lowerTwo_row_2119 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2119 j) = 460895975 := by decide
private theorem lowerTwo_row_2120 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2120 j) = 461263859 := by decide
private theorem lowerTwo_row_2121 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2121 j) = 461013398 := by decide
private theorem lowerTwo_row_2122 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2122 j) = 460941447 := by decide
private theorem lowerTwo_row_2123 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2123 j) = 461309075 := by decide
private theorem lowerTwo_row_2124 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2124 j) = 461676898 := by decide
private theorem lowerTwo_row_2125 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2125 j) = 461603683 := by decide
private theorem lowerTwo_row_2126 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2126 j) = 461351187 := by decide
private theorem lowerTwo_row_2127 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2127 j) = 461718743 := by decide
private theorem lowerTwo_row_2128 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2128 j) = 461643738 := by decide
private theorem lowerTwo_row_2129 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2129 j) = 462011355 := by decide
private theorem lowerTwo_row_2130 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2130 j) = 462379134 := by decide
private theorem lowerTwo_row_2131 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2131 j) = 461680707 := by decide
private theorem lowerTwo_row_2132 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2132 j) = 462048035 := by decide
private theorem lowerTwo_row_2133 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2133 j) = 462415576 := by decide
private theorem lowerTwo_row_2134 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2134 j) = 462337531 := by decide
private theorem lowerTwo_row_2135 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2135 j) = 462705093 := by decide
private theorem lowerTwo_row_2136 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2136 j) = 462448848 := by decide
private theorem lowerTwo_row_2137 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2137 j) = 462369021 := by decide
private theorem lowerTwo_row_2138 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2138 j) = 462736310 := by decide
private theorem lowerTwo_row_2139 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2139 j) = 463103775 := by decide
private theorem lowerTwo_row_2140 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2140 j) = 463022649 := by decide
private theorem lowerTwo_row_2141 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2141 j) = 462764336 := by decide
private theorem lowerTwo_row_2142 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2142 j) = 463131529 := by decide
private theorem lowerTwo_row_2143 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2143 j) = 463048610 := by decide
private theorem lowerTwo_row_2144 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2144 j) = 463415882 := by decide
private theorem lowerTwo_row_2145 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2145 j) = 463783345 := by decide
private theorem lowerTwo_row_2146 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2146 j) = 463071560 := by decide
private theorem lowerTwo_row_2147 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2147 j) = 463438593 := by decide
private theorem lowerTwo_row_2148 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2148 j) = 463805842 := by decide
private theorem lowerTwo_row_2149 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2149 j) = 463720008 := by decide
private theorem lowerTwo_row_2150 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2150 j) = 464087337 := by decide
private theorem lowerTwo_row_2151 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2151 j) = 463825342 := by decide
private theorem lowerTwo_row_2152 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2152 j) = 463737792 := by decide
private theorem lowerTwo_row_2153 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2153 j) = 464104868 := by decide
private theorem lowerTwo_row_2154 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2154 j) = 464472209 := by decide
private theorem lowerTwo_row_2155 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2155 j) = 464383423 := by decide
private theorem lowerTwo_row_2156 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2156 j) = 464119406 := by decide
private theorem lowerTwo_row_2157 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2157 j) = 464486501 := by decide
private theorem lowerTwo_row_2158 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2158 j) = 464395998 := by decide
private theorem lowerTwo_row_2159 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2159 j) = 464763162 := by decide
private theorem lowerTwo_row_2160 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2160 j) = 465130498 := by decide
private theorem lowerTwo_row_2161 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2161 j) = 464405510 := by decide
private theorem lowerTwo_row_2162 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2162 j) = 464772423 := by decide
private theorem lowerTwo_row_2163 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2163 j) = 465139563 := by decide
private theorem lowerTwo_row_2164 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2164 j) = 465046067 := by decide
private theorem lowerTwo_row_2165 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2165 j) = 465413274 := by decide
private theorem lowerTwo_row_2166 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2166 j) = 465145505 := by decide
private theorem lowerTwo_row_2167 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2167 j) = 465050262 := by decide
private theorem lowerTwo_row_2168 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2168 j) = 465417240 := by decide
private theorem lowerTwo_row_2169 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2169 j) = 465784402 := by decide
private theorem lowerTwo_row_2170 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2170 j) = 465687872 := by decide
private theorem lowerTwo_row_2171 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2171 j) = 465418073 := by decide
private theorem lowerTwo_row_2172 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2172 j) = 465784978 := by decide
private theorem lowerTwo_row_2173 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2173 j) = 465686689 := by decide
private theorem lowerTwo_row_2174 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2174 j) = 466053666 := by decide
private theorem lowerTwo_row_2175 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2175 j) = 466420891 := by decide
private theorem lowerTwo_row_2176 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2176 j) = 465682346 := by decide
private theorem lowerTwo_row_2177 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2177 j) = 466049095 := by decide
private theorem lowerTwo_row_2178 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2178 j) = 466416019 := by decide
private theorem lowerTwo_row_2179 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2179 j) = 466314681 := by decide
private theorem lowerTwo_row_2180 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2180 j) = 466681716 := by decide
private theorem lowerTwo_row_2181 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2181 j) = 466408030 := by decide
private theorem lowerTwo_row_2182 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2182 j) = 466304856 := by decide
private theorem lowerTwo_row_2183 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2183 j) = 466671599 := by decide
private theorem lowerTwo_row_2184 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2184 j) = 467038593 := by decide
private theorem lowerTwo_row_2185 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2185 j) = 466934106 := by decide
private theorem lowerTwo_row_2186 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2186 j) = 466658285 := by decide
private theorem lowerTwo_row_2187 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2187 j) = 467025015 := by decide
private theorem lowerTwo_row_2188 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2188 j) = 466918706 := by decide
private theorem lowerTwo_row_2189 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2189 j) = 467285475 := by decide
private theorem lowerTwo_row_2190 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2190 j) = 467652513 := by decide
private theorem lowerTwo_row_2191 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2191 j) = 466900003 := by decide
private theorem lowerTwo_row_2192 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2192 j) = 467266544 := by decide
private theorem lowerTwo_row_2193 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2193 j) = 467633311 := by decide
private theorem lowerTwo_row_2194 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2194 j) = 467523754 := by decide
private theorem lowerTwo_row_2195 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2195 j) = 467890570 := by decide
private theorem lowerTwo_row_2196 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2196 j) = 467610815 := by decide
private theorem lowerTwo_row_2197 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2197 j) = 467499378 := by decide
private theorem lowerTwo_row_2198 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2198 j) = 467865953 := by decide
private theorem lowerTwo_row_2199 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2199 j) = 468232733 := by decide
private theorem lowerTwo_row_2200 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2200 j) = 468119956 := by decide
private theorem lowerTwo_row_2201 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2201 j) = 467838015 := by decide
private theorem lowerTwo_row_2202 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2202 j) = 468204530 := by decide
private theorem lowerTwo_row_2203 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2203 j) = 468089963 := by decide
private theorem lowerTwo_row_2204 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2204 j) = 468456626 := by decide
private theorem lowerTwo_row_2205 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2205 j) = 468823476 := by decide
private theorem lowerTwo_row_2206 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2206 j) = 468056885 := by decide
private theorem lowerTwo_row_2207 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2207 j) = 468423293 := by decide
private theorem lowerTwo_row_2208 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2208 j) = 468789933 := by decide
private theorem lowerTwo_row_2209 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2209 j) = 468672373 := by decide
private theorem lowerTwo_row_2210 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2210 j) = 469039102 := by decide
private theorem lowerTwo_row_2211 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2211 j) = 468753211 := by decide
private theorem lowerTwo_row_2212 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2212 j) = 468633836 := by decide
private theorem lowerTwo_row_2213 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2213 j) = 469000350 := by decide
private theorem lowerTwo_row_2214 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2214 j) = 469367087 := by decide
private theorem lowerTwo_row_2215 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2215 j) = 469246436 := by decide
private theorem lowerTwo_row_2216 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2216 j) = 468958421 := by decide
private theorem lowerTwo_row_2217 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2217 j) = 469324950 := by decide
private theorem lowerTwo_row_2218 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2218 j) = 469202441 := by decide
private theorem lowerTwo_row_2219 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2219 j) = 469569037 := by decide
private theorem lowerTwo_row_2220 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2220 j) = 469935900 := by decide
private theorem lowerTwo_row_2221 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2221 j) = 469155223 := by decide
private theorem lowerTwo_row_2222 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2222 j) = 469521615 := by decide
private theorem lowerTwo_row_2223 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2223 j) = 469888235 := by decide
private theorem lowerTwo_row_2224 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2224 j) = 469762573 := by decide
private theorem lowerTwo_row_2225 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2225 j) = 470129271 := by decide
private theorem lowerTwo_row_2226 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2226 j) = 469837337 := by decide
private theorem lowerTwo_row_2227 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2227 j) = 469709781 := by decide
private theorem lowerTwo_row_2228 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2228 j) = 470076251 := by decide
private theorem lowerTwo_row_2229 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2229 j) = 470442942 := by decide
private theorem lowerTwo_row_2230 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2230 j) = 470314110 := by decide
private theorem lowerTwo_row_2231 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2231 j) = 470019925 := by decide
private theorem lowerTwo_row_2232 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2232 j) = 470386373 := by decide
private theorem lowerTwo_row_2233 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2233 j) = 470255624 := by decide
private theorem lowerTwo_row_2234 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2234 j) = 470622206 := by decide
private theorem lowerTwo_row_2235 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2235 j) = 470988995 := by decide
private theorem lowerTwo_row_2236 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2236 j) = 470193802 := by decide
private theorem lowerTwo_row_2237 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2237 j) = 470560127 := by decide
private theorem lowerTwo_row_2238 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2238 j) = 470926681 := by decide
private theorem lowerTwo_row_2239 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2239 j) = 470792689 := by decide
private theorem lowerTwo_row_2240 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2240 j) = 471159337 := by decide
private theorem lowerTwo_row_2241 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2241 j) = 470860988 := by decide
private theorem lowerTwo_row_2242 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2242 j) = 470725055 := by decide
private theorem lowerTwo_row_2243 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2243 j) = 471091481 := by decide
private theorem lowerTwo_row_2244 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2244 j) = 471458062 := by decide
private theorem lowerTwo_row_2245 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2245 j) = 471320774 := by decide
private theorem lowerTwo_row_2246 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2246 j) = 471020172 := by decide
private theorem lowerTwo_row_2247 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2247 j) = 471386525 := by decide
private theorem lowerTwo_row_2248 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2248 j) = 471247303 := by decide
private theorem lowerTwo_row_2249 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2249 j) = 471613743 := by decide
private theorem lowerTwo_row_2250 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2250 j) = 471980414 := by decide
private theorem lowerTwo_row_2251 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2251 j) = 471170342 := by decide
private theorem lowerTwo_row_2252 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2252 j) = 471536514 := by decide
private theorem lowerTwo_row_2253 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2253 j) = 471902952 := by decide
private theorem lowerTwo_row_2254 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2254 j) = 471760314 := by decide
private theorem lowerTwo_row_2255 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2255 j) = 472126825 := by decide
private theorem lowerTwo_row_2256 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2256 j) = 471821982 := by decide
private theorem lowerTwo_row_2257 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2257 j) = 471677358 := by decide
private theorem lowerTwo_row_2258 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2258 j) = 472043577 := by decide
private theorem lowerTwo_row_2259 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2259 j) = 472410084 := by decide
private theorem lowerTwo_row_2260 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2260 j) = 472264020 := by decide
private theorem lowerTwo_row_2261 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2261 j) = 471956816 := by decide
private theorem lowerTwo_row_2262 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2262 j) = 472323037 := by decide
private theorem lowerTwo_row_2263 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2263 j) = 472174956 := by decide
private theorem lowerTwo_row_2264 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2264 j) = 472541236 := by decide
private theorem lowerTwo_row_2265 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2265 j) = 472907785 := by decide
private theorem lowerTwo_row_2266 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2266 j) = 472082283 := by decide
private theorem lowerTwo_row_2267 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2267 j) = 472448304 := by decide
private theorem lowerTwo_row_2268 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2268 j) = 472814581 := by decide
private theorem lowerTwo_row_2269 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2269 j) = 472662995 := by decide
private theorem lowerTwo_row_2270 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2270 j) = 473029342 := by decide
private theorem lowerTwo_row_2271 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2271 j) = 472717804 := by decide
private theorem lowerTwo_row_2272 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2272 j) = 472564325 := by decide
private theorem lowerTwo_row_2273 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2273 j) = 472930502 := by decide
private theorem lowerTwo_row_2274 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2274 j) = 473296863 := by decide
private theorem lowerTwo_row_2275 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2275 j) = 472871847 := by decide
private theorem lowerTwo_row_2276 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2276 j) = 472287722 := by decide
private theorem lowerTwo_row_2277 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2277 j) = 472113550 := by decide
private theorem lowerTwo_row_2278 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2278 j) = 471686603 := by decide
private theorem lowerTwo_row_2279 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2279 j) = 471512582 := by decide
private theorem lowerTwo_row_2280 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2280 j) = 471608855 := by decide
private theorem lowerTwo_row_2281 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2281 j) = 470228002 := by decide
private theorem lowerTwo_row_2282 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2282 j) = 470323813 := by decide
private theorem lowerTwo_row_2283 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2283 j) = 470149816 := by decide
private theorem lowerTwo_row_2284 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2284 j) = 469719665 := by decide
private theorem lowerTwo_row_2285 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2285 j) = 469545827 := by decide
private theorem lowerTwo_row_2286 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2286 j) = 468957480 := by decide
private theorem lowerTwo_row_2287 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2287 j) = 468255331 := by decide
private theorem lowerTwo_row_2288 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2288 j) = 468351278 := by decide
private theorem lowerTwo_row_2289 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2289 j) = 468177482 := by decide
private theorem lowerTwo_row_2290 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2290 j) = 467744015 := by decide
private theorem lowerTwo_row_2291 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2291 j) = 466883264 := by decide
private theorem lowerTwo_row_2292 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2292 j) = 466979294 := by decide
private theorem lowerTwo_row_2293 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2293 j) = 466273819 := by decide
private theorem lowerTwo_row_2294 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2294 j) = 466369902 := by decide
private theorem lowerTwo_row_2295 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2295 j) = 466196276 := by decide
private theorem lowerTwo_row_2296 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2296 j) = 465070135 := by decide
private theorem lowerTwo_row_2297 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2297 j) = 464895966 := by decide
private theorem lowerTwo_row_2298 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2298 j) = 464992133 := by decide
private theorem lowerTwo_row_2299 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2299 j) = 464283260 := by decide
private theorem lowerTwo_row_2300 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2300 j) = 464379502 := by decide
private theorem lowerTwo_row_2301 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2301 j) = 463514367 := by decide
private theorem lowerTwo_row_2302 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2302 j) = 463073566 := by decide
private theorem lowerTwo_row_2303 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2303 j) = 462899519 := by decide
private theorem lowerTwo_row_2304 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2304 j) = 462995795 := by decide
private theorem lowerTwo_row_2305 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2305 j) = 462283455 := by decide
private theorem lowerTwo_row_2306 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2306 j) = 461685955 := by decide
private theorem lowerTwo_row_2307 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2307 j) = 461511912 := by decide
private theorem lowerTwo_row_2308 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2308 j) = 461067589 := by decide
private theorem lowerTwo_row_2309 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2309 j) = 460893652 := by decide
private theorem lowerTwo_row_2310 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2310 j) = 460990046 := by decide
private theorem lowerTwo_row_2311 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2311 j) = 459578028 := by decide
private theorem lowerTwo_row_2312 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2312 j) = 459673865 := by decide
private theorem lowerTwo_row_2313 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2313 j) = 459499886 := by decide
private theorem lowerTwo_row_2314 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2314 j) = 459052071 := by decide
private theorem lowerTwo_row_2315 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2315 j) = 458878217 := by decide
private theorem lowerTwo_row_2316 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2316 j) = 458276070 := by decide
private theorem lowerTwo_row_2317 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2317 j) = 457556115 := by decide
private theorem lowerTwo_row_2318 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2318 j) = 457652033 := by decide
private theorem lowerTwo_row_2319 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2319 j) = 457478140 := by decide
private theorem lowerTwo_row_2320 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2320 j) = 457026763 := by decide
private theorem lowerTwo_row_2321 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2321 j) = 456152001 := by decide
private theorem lowerTwo_row_2322 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2322 j) = 456247905 := by decide
private theorem lowerTwo_row_2323 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2323 j) = 455524284 := by decide
private theorem lowerTwo_row_2324 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2324 j) = 455620287 := by decide
private theorem lowerTwo_row_2325 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2325 j) = 455446446 := by decide
private theorem lowerTwo_row_2326 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2326 j) = 454288062 := by decide
private theorem lowerTwo_row_2327 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2327 j) = 454113649 := by decide
private theorem lowerTwo_row_2328 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2328 j) = 454209638 := by decide
private theorem lowerTwo_row_2329 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2329 j) = 453482292 := by decide
private theorem lowerTwo_row_2330 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2330 j) = 453578306 := by decide
private theorem lowerTwo_row_2331 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2331 j) = 452698824 := by decide
private theorem lowerTwo_row_2332 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2332 j) = 452239387 := by decide
private theorem lowerTwo_row_2333 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2333 j) = 452065001 := by decide
private theorem lowerTwo_row_2334 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2334 j) = 452161010 := by decide
private theorem lowerTwo_row_2335 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2335 j) = 451429913 := by decide
private theorem lowerTwo_row_2336 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2336 j) = 450817849 := by decide
private theorem lowerTwo_row_2337 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2337 j) = 450643427 := by decide
private theorem lowerTwo_row_2338 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2338 j) = 450180191 := by decide
private theorem lowerTwo_row_2339 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2339 j) = 450005843 := by decide
private theorem lowerTwo_row_2340 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2340 j) = 450101832 := by decide
private theorem lowerTwo_row_2341 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2341 j) = 448656355 := by decide
private theorem lowerTwo_row_2342 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2342 j) = 448751781 := by decide
private theorem lowerTwo_row_2343 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2343 j) = 448577309 := by decide
private theorem lowerTwo_row_2344 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2344 j) = 448110243 := by decide
private theorem lowerTwo_row_2345 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2345 j) = 447935876 := by decide
private theorem lowerTwo_row_2346 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2346 j) = 447318848 := by decide
private theorem lowerTwo_row_2347 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2347 j) = 446579373 := by decide
private theorem lowerTwo_row_2348 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2348 j) = 446674766 := by decide
private theorem lowerTwo_row_2349 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2349 j) = 446500264 := by decide
private theorem lowerTwo_row_2350 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2350 j) = 446029289 := by decide
private theorem lowerTwo_row_2351 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2351 j) = 445139389 := by decide
private theorem lowerTwo_row_2352 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2352 j) = 445234670 := by decide
private theorem lowerTwo_row_2353 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2353 j) = 444491235 := by decide
private theorem lowerTwo_row_2354 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2354 j) = 444586597 := by decide
private theorem lowerTwo_row_2355 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2355 j) = 444412038 := by decide
private theorem lowerTwo_row_2356 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2356 j) = 443219119 := by decide
private theorem lowerTwo_row_2357 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2357 j) = 443043960 := by decide
private theorem lowerTwo_row_2358 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2358 j) = 443139210 := by decide
private theorem lowerTwo_row_2359 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2359 j) = 442391688 := by decide
private theorem lowerTwo_row_2360 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2360 j) = 442486962 := by decide
private theorem lowerTwo_row_2361 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2361 j) = 441591926 := by decide
private theorem lowerTwo_row_2362 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2362 j) = 441112221 := by decide
private theorem lowerTwo_row_2363 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2363 j) = 440936922 := by decide
private theorem lowerTwo_row_2364 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2364 j) = 441032131 := by decide
private theorem lowerTwo_row_2365 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2365 j) = 440280506 := by decide
private theorem lowerTwo_row_2366 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2366 j) = 439652748 := by decide
private theorem lowerTwo_row_2367 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2367 j) = 439477387 := by decide
private theorem lowerTwo_row_2368 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2368 j) = 438993486 := by decide
private theorem lowerTwo_row_2369 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2369 j) = 438818118 := by decide
private theorem lowerTwo_row_2370 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2370 j) = 438913188 := by decide
private theorem lowerTwo_row_2371 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2371 j) = 437431880 := by decide
private theorem lowerTwo_row_2372 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2372 j) = 437526313 := by decide
private theorem lowerTwo_row_2373 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2373 j) = 437350813 := by decide
private theorem lowerTwo_row_2374 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2374 j) = 436862683 := by decide
private theorem lowerTwo_row_2375 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2375 j) = 436687215 := by decide
private theorem lowerTwo_row_2376 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2376 j) = 436054136 := by decide
private theorem lowerTwo_row_2377 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2377 j) = 435293359 := by decide
private theorem lowerTwo_row_2378 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2378 j) = 435387678 := by decide
private theorem lowerTwo_row_2379 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2379 j) = 435211972 := by decide
private theorem lowerTwo_row_2380 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2380 j) = 434719591 := by decide
private theorem lowerTwo_row_2381 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2381 j) = 433813358 := by decide
private theorem lowerTwo_row_2382 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2382 j) = 433907460 := by decide
private theorem lowerTwo_row_2383 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2383 j) = 433142338 := by decide
private theorem lowerTwo_row_2384 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2384 j) = 433236488 := by decide
private theorem lowerTwo_row_2385 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2385 j) = 433060608 := by decide
private theorem lowerTwo_row_2386 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2386 j) = 431830686 := by decide
private theorem lowerTwo_row_2387 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2387 j) = 431654176 := by decide
private theorem lowerTwo_row_2388 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2388 j) = 431748073 := by decide
private theorem lowerTwo_row_2389 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2389 j) = 430978564 := by decide
private theorem lowerTwo_row_2390 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2390 j) = 431072507 := by decide
private theorem lowerTwo_row_2391 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2391 j) = 430160668 := by decide
private theorem lowerTwo_row_2392 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2392 j) = 429658793 := by decide
private theorem lowerTwo_row_2393 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2393 j) = 429482032 := by decide
private theorem lowerTwo_row_2394 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2394 j) = 429575787 := by decide
private theorem lowerTwo_row_2395 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2395 j) = 428801743 := by decide
private theorem lowerTwo_row_2396 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2396 j) = 428157049 := by decide
private theorem lowerTwo_row_2397 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2397 j) = 427980093 := by decide
private theorem lowerTwo_row_2398 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2398 j) = 427473680 := by decide
private theorem lowerTwo_row_2399 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2399 j) = 427296694 := by decide
private theorem lowerTwo_row_2400 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2400 j) = 427390243 := by decide
private theorem lowerTwo_row_2401 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2401 j) = 425870498 := by decide
private theorem lowerTwo_row_2402 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2402 j) = 425963304 := by decide
private theorem lowerTwo_row_2403 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2403 j) = 425786109 := by decide
private theorem lowerTwo_row_2404 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2404 j) = 425275053 := by decide
private theorem lowerTwo_row_2405 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2405 j) = 425097824 := by decide
private theorem lowerTwo_row_2406 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2406 j) = 424447385 := by decide
private theorem lowerTwo_row_2407 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2407 j) = 423663338 := by decide
private theorem lowerTwo_row_2408 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2408 j) = 423755903 := by decide
private theorem lowerTwo_row_2409 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2409 j) = 423578421 := by decide
private theorem lowerTwo_row_2410 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2410 j) = 423062680 := by decide
private theorem lowerTwo_row_2411 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2411 j) = 422138731 := by decide
private theorem lowerTwo_row_2412 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2412 j) = 422231036 := by decide
private theorem lowerTwo_row_2413 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2413 j) = 421442252 := by decide
private theorem lowerTwo_row_2414 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2414 j) = 421534556 := by decide
private theorem lowerTwo_row_2415 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2415 j) = 421356728 := by decide
private theorem lowerTwo_row_2416 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2416 j) = 420087090 := by decide
private theorem lowerTwo_row_2417 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2417 j) = 419908513 := by decide
private theorem lowerTwo_row_2418 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2418 j) = 420000526 := by decide
private theorem lowerTwo_row_2419 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2419 j) = 419206908 := by decide
private theorem lowerTwo_row_2420 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2420 j) = 419298886 := by decide
private theorem lowerTwo_row_2421 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2421 j) = 418368838 := by decide
private theorem lowerTwo_row_2422 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2422 j) = 417842770 := by decide
private theorem lowerTwo_row_2423 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2423 j) = 417663849 := by decide
private theorem lowerTwo_row_2424 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2424 j) = 417755546 := by decide
private theorem lowerTwo_row_2425 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2425 j) = 416957003 := by decide
private theorem lowerTwo_row_2426 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2426 j) = 416293996 := by decide
private theorem lowerTwo_row_2427 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2427 j) = 416114766 := by decide
private theorem lowerTwo_row_2428 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2428 j) = 415583739 := by decide
private theorem lowerTwo_row_2429 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2429 j) = 415404428 := by decide
private theorem lowerTwo_row_2430 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2430 j) = 415495765 := by decide
private theorem lowerTwo_row_2431 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2431 j) = 413934785 := by decide
private theorem lowerTwo_row_2432 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2432 j) = 414025330 := by decide
private theorem lowerTwo_row_2433 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2433 j) = 413845708 := by decide
private theorem lowerTwo_row_2434 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2434 j) = 413309640 := by decide
private theorem lowerTwo_row_2435 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2435 j) = 413129907 := by decide
private theorem lowerTwo_row_2436 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2436 j) = 412460705 := by decide
private theorem lowerTwo_row_2437 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2437 j) = 411651249 := by decide
private theorem lowerTwo_row_2438 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2438 j) = 411741407 := by decide
private theorem lowerTwo_row_2439 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2439 j) = 411561360 := by decide
private theorem lowerTwo_row_2440 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2440 j) = 411020150 := by decide
private theorem lowerTwo_row_2441 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2441 j) = 410077015 := by decide
private theorem lowerTwo_row_2442 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2442 j) = 410166819 := by decide
private theorem lowerTwo_row_2443 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2443 j) = 409352143 := by decide
private theorem lowerTwo_row_2444 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2444 j) = 409441914 := by decide
private theorem lowerTwo_row_2445 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2445 j) = 409261422 := by decide
private theorem lowerTwo_row_2446 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2446 j) = 407949082 := by decide
private theorem lowerTwo_row_2447 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2447 j) = 407767758 := by decide
private theorem lowerTwo_row_2448 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2448 j) = 407857157 := by decide
private theorem lowerTwo_row_2449 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2449 j) = 407037177 := by decide
private theorem lowerTwo_row_2450 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2450 j) = 407126435 := by decide
private theorem lowerTwo_row_2451 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2451 j) = 406176765 := by decide
private theorem lowerTwo_row_2452 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2452 j) = 405624254 := by decide
private theorem lowerTwo_row_2453 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2453 j) = 405442405 := by decide
private theorem lowerTwo_row_2454 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2454 j) = 405531295 := by decide
private theorem lowerTwo_row_2455 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2455 j) = 404705938 := by decide
private theorem lowerTwo_row_2456 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2456 j) = 404023174 := by decide
private theorem lowerTwo_row_2457 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2457 j) = 403840907 := by decide
private theorem lowerTwo_row_2458 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2458 j) = 403282980 := by decide
private theorem lowerTwo_row_2459 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2459 j) = 403100583 := by decide
private theorem lowerTwo_row_2460 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2460 j) = 403188969 := by decide
private theorem lowerTwo_row_2461 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2461 j) = 401583656 := by decide
private theorem lowerTwo_row_2462 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2462 j) = 401671184 := by decide
private theorem lowerTwo_row_2463 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2463 j) = 401488369 := by decide
private theorem lowerTwo_row_2464 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2464 j) = 400924907 := by decide
private theorem lowerTwo_row_2465 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2465 j) = 400741956 := by decide
private theorem lowerTwo_row_2466 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2466 j) = 400052431 := by decide
private theorem lowerTwo_row_2467 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2467 j) = 399215203 := by decide
private theorem lowerTwo_row_2468 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2468 j) = 399302160 := by decide
private theorem lowerTwo_row_2469 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2469 j) = 399118779 := by decide
private theorem lowerTwo_row_2470 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2470 j) = 398549693 := by decide
private theorem lowerTwo_row_2471 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2471 j) = 397585812 := by decide
private theorem lowerTwo_row_2472 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2472 j) = 397672337 := by decide
private theorem lowerTwo_row_2473 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2473 j) = 396829389 := by decide
private theorem lowerTwo_row_2474 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2474 j) = 396915792 := by decide
private theorem lowerTwo_row_2475 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2475 j) = 396731791 := by decide
private theorem lowerTwo_row_2476 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2476 j) = 395373674 := by decide
private theorem lowerTwo_row_2477 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2477 j) = 395188705 := by decide
private theorem lowerTwo_row_2478 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2478 j) = 395274641 := by decide
private theorem lowerTwo_row_2479 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2479 j) = 394425855 := by decide
private theorem lowerTwo_row_2480 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2480 j) = 394511675 := by decide
private theorem lowerTwo_row_2481 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2481 j) = 393540716 := by decide
private theorem lowerTwo_row_2482 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2482 j) = 392959277 := by decide
private theorem lowerTwo_row_2483 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2483 j) = 392773679 := by decide
private theorem lowerTwo_row_2484 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2484 j) = 392858968 := by decide
private theorem lowerTwo_row_2485 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2485 j) = 392004263 := by decide
private theorem lowerTwo_row_2486 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2486 j) = 391300123 := by decide
private theorem lowerTwo_row_2487 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2487 j) = 391113951 := by decide
private theorem lowerTwo_row_2488 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2488 j) = 390526604 := by decide
private theorem lowerTwo_row_2489 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2489 j) = 390340306 := by decide
private theorem lowerTwo_row_2490 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2490 j) = 390424890 := by decide
private theorem lowerTwo_row_2491 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2491 j) = 388771856 := by decide
private theorem lowerTwo_row_2492 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2492 j) = 388855508 := by decide
private theorem lowerTwo_row_2493 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2493 j) = 388668602 := by decide
private theorem lowerTwo_row_2494 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2494 j) = 388075235 := by decide
private theorem lowerTwo_row_2495 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2495 j) = 387888142 := by decide
private theorem lowerTwo_row_2496 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2496 j) = 387176672 := by decide
private theorem lowerTwo_row_2497 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2497 j) = 386309021 := by decide
private theorem lowerTwo_row_2498 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2498 j) = 386391973 := by decide
private theorem lowerTwo_row_2499 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2499 j) = 386204329 := by decide
private theorem lowerTwo_row_2500 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2500 j) = 385604761 := by decide
private theorem lowerTwo_row_2501 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2501 j) = 384618407 := by decide
private theorem lowerTwo_row_2502 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2502 j) = 384700790 := by decide
private theorem lowerTwo_row_2503 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2503 j) = 383826887 := by decide
private theorem lowerTwo_row_2504 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2504 j) = 383909040 := by decide
private theorem lowerTwo_row_2505 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2505 j) = 383720619 := by decide
private theorem lowerTwo_row_2506 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2506 j) = 382313193 := by decide
private theorem lowerTwo_row_2507 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2507 j) = 382123697 := by decide
private theorem lowerTwo_row_2508 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2508 j) = 382205315 := by decide
private theorem lowerTwo_row_2509 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2509 j) = 381325011 := by decide
private theorem lowerTwo_row_2510 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2510 j) = 381406397 := by decide
private theorem lowerTwo_row_2511 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2511 j) = 380412393 := by decide
private theorem lowerTwo_row_2512 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2512 j) = 379799347 := by decide
private theorem lowerTwo_row_2513 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2513 j) = 379608996 := by decide
private theorem lowerTwo_row_2514 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2514 j) = 379689760 := by decide
private theorem lowerTwo_row_2515 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2515 j) = 378802983 := by decide
private theorem lowerTwo_row_2516 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2516 j) = 378075673 := by decide
private theorem lowerTwo_row_2517 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2517 j) = 377884676 := by decide
private theorem lowerTwo_row_2518 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2518 j) = 377265112 := by decide
private theorem lowerTwo_row_2519 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2519 j) = 377073903 := by decide
private theorem lowerTwo_row_2520 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2520 j) = 377153801 := by decide
private theorem lowerTwo_row_2521 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2521 j) = 375449353 := by decide
private theorem lowerTwo_row_2522 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2522 j) = 375528195 := by decide
private theorem lowerTwo_row_2523 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2523 j) = 375336274 := by decide
private theorem lowerTwo_row_2524 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2524 j) = 374710102 := by decide
private theorem lowerTwo_row_2525 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2525 j) = 374517931 := by decide
private theorem lowerTwo_row_2526 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2526 j) = 373782637 := by decide
private theorem lowerTwo_row_2527 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2527 j) = 372881703 := by decide
private theorem lowerTwo_row_2528 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2528 j) = 372959617 := by decide
private theorem lowerTwo_row_2529 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2529 j) = 372766734 := by decide
private theorem lowerTwo_row_2530 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2530 j) = 372133810 := by decide
private theorem lowerTwo_row_2531 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2531 j) = 371123152 := by decide
private theorem lowerTwo_row_2532 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2532 j) = 371200360 := by decide
private theorem lowerTwo_row_2533 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2533 j) = 370292546 := by decide
private theorem lowerTwo_row_2534 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2534 j) = 370369517 := by decide
private theorem lowerTwo_row_2535 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2535 j) = 370175639 := by decide
private theorem lowerTwo_row_2536 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2536 j) = 368715051 := by decide
private theorem lowerTwo_row_2537 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2537 j) = 368519999 := by decide
private theorem lowerTwo_row_2538 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2538 j) = 368596263 := by decide
private theorem lowerTwo_row_2539 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2539 j) = 367681446 := by decide
private theorem lowerTwo_row_2540 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2540 j) = 367757406 := by decide
private theorem lowerTwo_row_2541 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2541 j) = 366738437 := by decide
private theorem lowerTwo_row_2542 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2542 j) = 366090735 := by decide
private theorem lowerTwo_row_2543 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2543 j) = 365894627 := by decide
private theorem lowerTwo_row_2544 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2544 j) = 365969863 := by decide
private theorem lowerTwo_row_2545 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2545 j) = 365047923 := by decide
private theorem lowerTwo_row_2546 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2546 j) = 364295472 := by decide
private theorem lowerTwo_row_2547 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2547 j) = 364098567 := by decide
private theorem lowerTwo_row_2548 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2548 j) = 363443722 := by decide
private theorem lowerTwo_row_2549 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2549 j) = 363246515 := by decide
private theorem lowerTwo_row_2550 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2550 j) = 363320680 := by decide
private theorem lowerTwo_row_2551 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2551 j) = 361560773 := by decide
private theorem lowerTwo_row_2552 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2552 j) = 361633730 := by decide
private theorem lowerTwo_row_2553 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2553 j) = 361435695 := by decide
private theorem lowerTwo_row_2554 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2554 j) = 360773572 := by decide
private theorem lowerTwo_row_2555 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2555 j) = 360575208 := by decide
private theorem lowerTwo_row_2556 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2556 j) = 359814156 := by decide
private theorem lowerTwo_row_2557 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2557 j) = 358876702 := by decide
private theorem lowerTwo_row_2558 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2558 j) = 358948502 := by decide
private theorem lowerTwo_row_2559 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2559 j) = 358749270 := by decide
private theorem lowerTwo_row_2560 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2560 j) = 358079763 := by decide
private theorem lowerTwo_row_2561 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2561 j) = 357042717 := by decide
private theorem lowerTwo_row_2562 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2562 j) = 357113668 := by decide
private theorem lowerTwo_row_2563 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2563 j) = 356168680 := by decide
private theorem lowerTwo_row_2564 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2564 j) = 356239308 := by decide
private theorem lowerTwo_row_2565 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2565 j) = 356038833 := by decide
private theorem lowerTwo_row_2566 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2566 j) = 354520902 := by decide
private theorem lowerTwo_row_2567 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2567 j) = 354319129 := by decide
private theorem lowerTwo_row_2568 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2568 j) = 354388904 := by decide
private theorem lowerTwo_row_2569 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2569 j) = 353436231 := by decide
private theorem lowerTwo_row_2570 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2570 j) = 353505608 := by decide
private theorem lowerTwo_row_2571 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2571 j) = 352459551 := by decide
private theorem lowerTwo_row_2572 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2572 j) = 351773865 := by decide
private theorem lowerTwo_row_2573 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2573 j) = 351570793 := by decide
private theorem lowerTwo_row_2574 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2574 j) = 351639295 := by decide
private theorem lowerTwo_row_2575 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2575 j) = 350678781 := by decide
private theorem lowerTwo_row_2576 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2576 j) = 350203952 := by decide
private theorem lowerTwo_row_2577 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2577 j) = 350610097 := by decide
private theorem lowerTwo_row_2578 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2578 j) = 350221735 := by decide
private theorem lowerTwo_row_2579 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2579 j) = 350322595 := by decide
private theorem lowerTwo_row_2580 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2580 j) = 351001128 := by decide
private theorem lowerTwo_row_2581 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2581 j) = 349486968 := by decide
private theorem lowerTwo_row_2582 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2582 j) = 349858564 := by decide
private theorem lowerTwo_row_2583 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2583 j) = 350265702 := by decide
private theorem lowerTwo_row_2584 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2584 j) = 349870221 := by decide
private theorem lowerTwo_row_2585 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2585 j) = 349970590 := by decide
private theorem lowerTwo_row_2586 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2586 j) = 349795363 := by decide
private theorem lowerTwo_row_2587 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2587 j) = 349124346 := by decide
private theorem lowerTwo_row_2588 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2588 j) = 349495441 := by decide
private theorem lowerTwo_row_2589 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2589 j) = 349903583 := by decide
private theorem lowerTwo_row_2590 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2590 j) = 349500896 := by decide
private theorem lowerTwo_row_2591 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2591 j) = 348742318 := by decide
private theorem lowerTwo_row_2592 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2592 j) = 349421978 := by decide
private theorem lowerTwo_row_2593 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2593 j) = 348743603 := by decide
private theorem lowerTwo_row_2594 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2594 j) = 349114174 := by decide
private theorem lowerTwo_row_2595 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2595 j) = 349523260 := by decide
private theorem lowerTwo_row_2596 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2596 j) = 348251260 := by decide
private theorem lowerTwo_row_2597 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2597 j) = 348349484 := by decide
private theorem lowerTwo_row_2598 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2598 j) = 349030189 := by decide
private theorem lowerTwo_row_2599 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2599 j) = 348344300 := by decide
private theorem lowerTwo_row_2600 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2600 j) = 348714295 := by decide
private theorem lowerTwo_row_2601 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2601 j) = 348258775 := by decide
private theorem lowerTwo_row_2602 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2602 j) = 347840237 := by decide
private theorem lowerTwo_row_2603 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2603 j) = 347937812 := by decide
private theorem lowerTwo_row_2604 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2604 j) = 348619495 := by decide
private theorem lowerTwo_row_2605 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2605 j) = 347925953 := by decide
private theorem lowerTwo_row_2606 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2606 j) = 347426124 := by decide
private theorem lowerTwo_row_2607 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2607 j) = 347836118 := by decide
private theorem lowerTwo_row_2608 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2608 j) = 347409902 := by decide
private theorem lowerTwo_row_2609 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2609 j) = 347506771 := by decide
private theorem lowerTwo_row_2610 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2610 j) = 348189433 := by decide
private theorem lowerTwo_row_2611 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2611 j) = 346615174 := by decide
private theorem lowerTwo_row_2612 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2612 j) = 346982967 := by decide
private theorem lowerTwo_row_2613 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2613 j) = 347393850 := by decide
private theorem lowerTwo_row_2614 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2614 j) = 346959764 := by decide
private theorem lowerTwo_row_2615 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2615 j) = 347055946 := by decide
private theorem lowerTwo_row_2616 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2616 j) = 346862936 := by decide
private theorem lowerTwo_row_2617 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2617 j) = 346152590 := by decide
private theorem lowerTwo_row_2618 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2618 j) = 346519711 := by decide
private theorem lowerTwo_row_2619 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2619 j) = 346931416 := by decide
private theorem lowerTwo_row_2620 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2620 j) = 346489357 := by decide
private theorem lowerTwo_row_2621 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2621 j) = 345704443 := by decide
private theorem lowerTwo_row_2622 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2622 j) = 346387924 := by decide
private theorem lowerTwo_row_2623 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2623 j) = 345669478 := by decide
private theorem lowerTwo_row_2624 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2624 j) = 346035859 := by decide
private theorem lowerTwo_row_2625 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2625 j) = 346448378 := by decide
private theorem lowerTwo_row_2626 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2626 j) = 345114106 := by decide
private theorem lowerTwo_row_2627 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2627 j) = 345207700 := by decide
private theorem lowerTwo_row_2628 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2628 j) = 345892018 := by decide
private theorem lowerTwo_row_2629 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2629 j) = 345165275 := by decide
private theorem lowerTwo_row_2630 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2630 j) = 345530857 := by decide
private theorem lowerTwo_row_2631 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2631 j) = 345056277 := by decide
private theorem lowerTwo_row_2632 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2632 j) = 344596789 := by decide
private theorem lowerTwo_row_2633 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2633 j) = 344689522 := by decide
private theorem lowerTwo_row_2634 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2634 j) = 345374649 := by decide
private theorem lowerTwo_row_2635 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2635 j) = 344639505 := by decide
private theorem lowerTwo_row_2636 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2636 j) = 344112530 := by decide
private theorem lowerTwo_row_2637 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2637 j) = 344525575 := by decide
private theorem lowerTwo_row_2638 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2638 j) = 344057596 := by decide
private theorem lowerTwo_row_2639 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2639 j) = 344149375 := by decide
private theorem lowerTwo_row_2640 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2640 j) = 344835333 := by decide
private theorem lowerTwo_row_2641 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2641 j) = 343195968 := by decide
private theorem lowerTwo_row_2642 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2642 j) = 343558779 := by decide
private theorem lowerTwo_row_2643 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2643 j) = 343972575 := by decide
private theorem lowerTwo_row_2644 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2644 j) = 343495935 := by decide
private theorem lowerTwo_row_2645 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2645 j) = 343586743 := by decide
private theorem lowerTwo_row_2646 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2646 j) = 343374009 := by decide
private theorem lowerTwo_row_2647 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2647 j) = 342620360 := by decide
private theorem lowerTwo_row_2648 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2648 j) = 342982255 := by decide
private theorem lowerTwo_row_2649 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2649 j) = 343396707 := by decide
private theorem lowerTwo_row_2650 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2650 j) = 342911244 := by decide
private theorem lowerTwo_row_2651 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2651 j) = 342097674 := by decide
private theorem lowerTwo_row_2652 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2652 j) = 342784076 := by decide
private theorem lowerTwo_row_2653 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2653 j) = 342021437 := by decide
private theorem lowerTwo_row_2654 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2654 j) = 342382328 := by decide
private theorem lowerTwo_row_2655 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2655 j) = 342797434 := by decide
private theorem lowerTwo_row_2656 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2656 j) = 341395611 := by decide
private theorem lowerTwo_row_2657 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2657 j) = 341483310 := by decide
private theorem lowerTwo_row_2658 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2658 j) = 342170384 := by decide
private theorem lowerTwo_row_2659 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2659 j) = 341398588 := by decide
private theorem lowerTwo_row_2660 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2660 j) = 341758440 := by decide
private theorem lowerTwo_row_2661 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2661 j) = 341262801 := by decide
private theorem lowerTwo_row_2662 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2662 j) = 340758121 := by decide
private theorem lowerTwo_row_2663 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2663 j) = 340844605 := by decide
private theorem lowerTwo_row_2664 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2664 j) = 341532311 := by decide
private theorem lowerTwo_row_2665 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2665 j) = 340751197 := by decide
private theorem lowerTwo_row_2666 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2666 j) = 340194606 := by decide
private theorem lowerTwo_row_2667 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2667 j) = 340609776 := by decide
private theorem lowerTwo_row_2668 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2668 j) = 340095705 := by decide
private theorem lowerTwo_row_2669 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2669 j) = 340181020 := by decide
private theorem lowerTwo_row_2670 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2670 j) = 340869339 := by decide
private theorem lowerTwo_row_2671 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2671 j) = 339159271 := by decide
private theorem lowerTwo_row_2672 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2672 j) = 339515787 := by decide
private theorem lowerTwo_row_2673 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2673 j) = 339931473 := by decide
private theorem lowerTwo_row_2674 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2674 j) = 339407818 := by decide
private theorem lowerTwo_row_2675 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2675 j) = 339491822 := by decide
private theorem lowerTwo_row_2676 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2676 j) = 339257246 := by decide
private theorem lowerTwo_row_2677 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2677 j) = 338455758 := by decide
private theorem lowerTwo_row_2678 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2678 j) = 338811004 := by decide
private theorem lowerTwo_row_2679 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2679 j) = 339227200 := by decide
private theorem lowerTwo_row_2680 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2680 j) = 338693767 := by decide
private theorem lowerTwo_row_2681 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2681 j) = 337848846 := by decide
private theorem lowerTwo_row_2682 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2682 j) = 338537188 := by decide
private theorem lowerTwo_row_2683 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2683 j) = 337725728 := by decide
private theorem lowerTwo_row_2684 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2684 j) = 338079732 := by decide
private theorem lowerTwo_row_2685 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2685 j) = 338496315 := by decide
private theorem lowerTwo_row_2686 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2686 j) = 337021124 := by decide
private theorem lowerTwo_row_2687 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2687 j) = 337101349 := by decide
private theorem lowerTwo_row_2688 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2688 j) = 337790147 := by decide
private theorem lowerTwo_row_2689 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2689 j) = 336968533 := by decide
private theorem lowerTwo_row_2690 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2690 j) = 337321190 := by decide
private theorem lowerTwo_row_2691 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2691 j) = 336802173 := by decide
private theorem lowerTwo_row_2692 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2692 j) = 336247446 := by decide
private theorem lowerTwo_row_2693 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2693 j) = 336326239 := by decide
private theorem lowerTwo_row_2694 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2694 j) = 337015451 := by decide
private theorem lowerTwo_row_2695 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2695 j) = 336183480 := by decide
private theorem lowerTwo_row_2696 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2696 j) = 335594492 := by decide
private theorem lowerTwo_row_2697 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2697 j) = 336010667 := by decide
private theorem lowerTwo_row_2698 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2698 j) = 335445557 := by decide
private theorem lowerTwo_row_2699 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2699 j) = 335522792 := by decide
private theorem lowerTwo_row_2700 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2700 j) = 336212363 := by decide
private theorem lowerTwo_row_2701 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2701 j) = 334425346 := by decide
private theorem lowerTwo_row_2702 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2702 j) = 334773952 := by decide
private theorem lowerTwo_row_2703 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2703 j) = 335190386 := by decide
private theorem lowerTwo_row_2704 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2704 j) = 334614673 := by decide
private theorem lowerTwo_row_2705 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2705 j) = 334690274 := by decide
private theorem lowerTwo_row_2706 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2706 j) = 334431441 := by decide
private theorem lowerTwo_row_2707 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2707 j) = 333576939 := by decide
private theorem lowerTwo_row_2708 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2708 j) = 333923961 := by decide
private theorem lowerTwo_row_2709 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2709 j) = 334340639 := by decide
private theorem lowerTwo_row_2710 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2710 j) = 333754049 := by decide
private theorem lowerTwo_row_2711 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2711 j) = 332874869 := by decide
private theorem lowerTwo_row_2712 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2712 j) = 333563926 := by decide
private theorem lowerTwo_row_2713 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2713 j) = 332698396 := by decide
private theorem lowerTwo_row_2714 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2714 j) = 333043752 := by decide
private theorem lowerTwo_row_2715 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2715 j) = 333460618 := by decide
private theorem lowerTwo_row_2716 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2716 j) = 331905470 := by decide
private theorem lowerTwo_row_2717 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2717 j) = 331976502 := by decide
private theorem lowerTwo_row_2718 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2718 j) = 332665758 := by decide
private theorem lowerTwo_row_2719 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2719 j) = 331788925 := by decide
private theorem lowerTwo_row_2720 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2720 j) = 332132613 := by decide
private theorem lowerTwo_row_2721 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2721 j) = 331587657 := by decide
private theorem lowerTwo_row_2722 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2722 j) = 330977506 := by decide
private theorem lowerTwo_row_2723 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2723 j) = 331046712 := by decide
private theorem lowerTwo_row_2724 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2724 j) = 331736139 := by decide
private theorem lowerTwo_row_2725 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2725 j) = 330847758 := by decide
private theorem lowerTwo_row_2726 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2726 j) = 330223322 := by decide
private theorem lowerTwo_row_2727 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2727 j) = 330639125 := by decide
private theorem lowerTwo_row_2728 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2728 j) = 330017413 := by decide
private theorem lowerTwo_row_2729 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2729 j) = 330084717 := by decide
private theorem lowerTwo_row_2730 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2730 j) = 329763548 := by decide
private theorem lowerTwo_row_2731 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2731 j) = 327892938 := by decide
private theorem lowerTwo_row_2732 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2732 j) = 328189774 := by decide
private theorem lowerTwo_row_2733 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2733 j) = 328523080 := by decide
private theorem lowerTwo_row_2734 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2734 j) = 328861798 := by decide
private theorem lowerTwo_row_2735 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2735 j) = 328886583 := by decide
private theorem lowerTwo_row_2736 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2736 j) = 329495650 := by decide
private theorem lowerTwo_row_2737 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2737 j) = 329562336 := by decide
private theorem lowerTwo_row_2738 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2738 j) = 329861440 := by decide
private theorem lowerTwo_row_2739 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2739 j) = 330199904 := by decide
private theorem lowerTwo_row_2740 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2740 j) = 330540940 := by decide
private theorem lowerTwo_row_2741 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2741 j) = 330567955 := by decide
private theorem lowerTwo_row_2742 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2742 j) = 331182267 := by decide
private theorem lowerTwo_row_2743 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2743 j) = 331251187 := by decide
private theorem lowerTwo_row_2744 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2744 j) = 331552573 := by decide
private theorem lowerTwo_row_2745 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2745 j) = 331896291 := by decide
private theorem lowerTwo_row_2746 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2746 j) = 332239632 := by decide
private theorem lowerTwo_row_2747 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2747 j) = 332268864 := by decide
private theorem lowerTwo_row_2748 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2748 j) = 332888575 := by decide
private theorem lowerTwo_row_2749 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2749 j) = 332959698 := by decide
private theorem lowerTwo_row_2750 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2750 j) = 333263417 := by decide
private theorem lowerTwo_row_2751 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2751 j) = 333612438 := by decide
private theorem lowerTwo_row_2752 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2752 j) = 333958107 := by decide
private theorem lowerTwo_row_2753 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2753 j) = 333989603 := by decide
private theorem lowerTwo_row_2754 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2754 j) = 334614696 := by decide
private theorem lowerTwo_row_2755 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2755 j) = 334688129 := by decide
private theorem lowerTwo_row_2756 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2756 j) = 334994239 := by decide
private theorem lowerTwo_row_2757 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2757 j) = 335348532 := by decide
private theorem lowerTwo_row_2758 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2758 j) = 335696587 := by decide
private theorem lowerTwo_row_2759 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2759 j) = 335730399 := by decide
private theorem lowerTwo_row_2760 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2760 j) = 336360928 := by decide
private theorem lowerTwo_row_2761 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2761 j) = 336436662 := by decide
private theorem lowerTwo_row_2762 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2762 j) = 336745138 := by decide
private theorem lowerTwo_row_2763 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2763 j) = 337104844 := by decide
private theorem lowerTwo_row_2764 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2764 j) = 337455348 := by decide
private theorem lowerTwo_row_2765 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2765 j) = 337491442 := by decide
private theorem lowerTwo_row_2766 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2766 j) = 338127382 := by decide
private theorem lowerTwo_row_2767 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2767 j) = 338205396 := by decide
private theorem lowerTwo_row_2768 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2768 j) = 338516242 := by decide
private theorem lowerTwo_row_2769 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2769 j) = 338881095 := by decide
private theorem lowerTwo_row_2770 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2770 j) = 339233885 := by decide
private theorem lowerTwo_row_2771 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2771 j) = 339272182 := by decide
private theorem lowerTwo_row_2772 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2772 j) = 339913264 := by decide
private theorem lowerTwo_row_2773 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2773 j) = 339993523 := by decide
private theorem lowerTwo_row_2774 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2774 j) = 340306612 := by decide
private theorem lowerTwo_row_2775 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2775 j) = 340676603 := by decide
private theorem lowerTwo_row_2776 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2776 j) = 341031722 := by decide
private theorem lowerTwo_row_2777 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2777 j) = 341072213 := by decide
private theorem lowerTwo_row_2778 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2778 j) = 341718560 := by decide
private theorem lowerTwo_row_2779 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2779 j) = 341801011 := by decide
private theorem lowerTwo_row_2780 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2780 j) = 342116429 := by decide
private theorem lowerTwo_row_2781 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2781 j) = 342491614 := by decide
private theorem lowerTwo_row_2782 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2782 j) = 342849033 := by decide
private theorem lowerTwo_row_2783 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2783 j) = 342891766 := by decide
private theorem lowerTwo_row_2784 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2784 j) = 343543417 := by decide
private theorem lowerTwo_row_2785 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2785 j) = 343628133 := by decide
private theorem lowerTwo_row_2786 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2786 j) = 343945888 := by decide
private theorem lowerTwo_row_2787 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2787 j) = 344326310 := by decide
private theorem lowerTwo_row_2788 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2788 j) = 344686084 := by decide
private theorem lowerTwo_row_2789 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2789 j) = 344731093 := by decide
private theorem lowerTwo_row_2790 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2790 j) = 345388072 := by decide
private theorem lowerTwo_row_2791 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2791 j) = 345475090 := by decide
private theorem lowerTwo_row_2792 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2792 j) = 345795216 := by decide
private theorem lowerTwo_row_2793 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2793 j) = 346180920 := by decide
private theorem lowerTwo_row_2794 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2794 j) = 346543070 := by decide
private theorem lowerTwo_row_2795 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2795 j) = 346590384 := by decide
private theorem lowerTwo_row_2796 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2796 j) = 347252772 := by decide
private theorem lowerTwo_row_2797 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2797 j) = 347342106 := by decide
private theorem lowerTwo_row_2798 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2798 j) = 347664629 := by decide
private theorem lowerTwo_row_2799 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2799 j) = 348055657 := by decide
private theorem lowerTwo_row_2800 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2800 j) = 348420263 := by decide
private theorem lowerTwo_row_2801 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2801 j) = 348469875 := by decide
private theorem lowerTwo_row_2802 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2802 j) = 349137733 := by decide
private theorem lowerTwo_row_2803 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2803 j) = 349229422 := by decide
private theorem lowerTwo_row_2804 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2804 j) = 349554361 := by decide
private theorem lowerTwo_row_2805 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2805 j) = 349950797 := by decide
private theorem lowerTwo_row_2806 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2806 j) = 350317876 := by decide
private theorem lowerTwo_row_2807 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2807 j) = 350369809 := by decide
private theorem lowerTwo_row_2808 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2808 j) = 351043220 := by decide
private theorem lowerTwo_row_2809 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2809 j) = 351137264 := by decide
private theorem lowerTwo_row_2810 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2810 j) = 351464645 := by decide
private theorem lowerTwo_row_2811 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2811 j) = 351866579 := by decide
private theorem lowerTwo_row_2812 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2812 j) = 352236125 := by decide
private theorem lowerTwo_row_2813 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2813 j) = 352290414 := by decide
private theorem lowerTwo_row_2814 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2814 j) = 352969447 := by decide
private theorem lowerTwo_row_2815 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2815 j) = 353065866 := by decide
private theorem lowerTwo_row_2816 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2816 j) = 353395714 := by decide
private theorem lowerTwo_row_2817 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2817 j) = 353803208 := by decide
private theorem lowerTwo_row_2818 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2818 j) = 354175249 := by decide
private theorem lowerTwo_row_2819 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2819 j) = 354231956 := by decide
private theorem lowerTwo_row_2820 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2820 j) = 354916651 := by decide
private theorem lowerTwo_row_2821 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2821 j) = 355015508 := by decide
private theorem lowerTwo_row_2822 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2822 j) = 355347868 := by decide
private theorem lowerTwo_row_2823 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2823 j) = 355760962 := by decide
private theorem lowerTwo_row_2824 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2824 j) = 356135524 := by decide
private theorem lowerTwo_row_2825 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2825 j) = 356194676 := by decide
private theorem lowerTwo_row_2826 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2826 j) = 356885088 := by decide
private theorem lowerTwo_row_2827 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2827 j) = 356986401 := by decide
private theorem lowerTwo_row_2828 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2828 j) = 357321322 := by decide
private theorem lowerTwo_row_2829 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2829 j) = 357740073 := by decide
private theorem lowerTwo_row_2830 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2830 j) = 358117188 := by decide
private theorem lowerTwo_row_2831 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2831 j) = 358178832 := by decide
private theorem lowerTwo_row_2832 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2832 j) = 358875023 := by decide
private theorem lowerTwo_row_2833 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2833 j) = 358978797 := by decide
private theorem lowerTwo_row_2834 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2834 j) = 359316306 := by decide
private theorem lowerTwo_row_2835 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2835 j) = 359740761 := by decide
private theorem lowerTwo_row_2836 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2836 j) = 360120429 := by decide
private theorem lowerTwo_row_2837 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2837 j) = 360184490 := by decide
private theorem lowerTwo_row_2838 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2838 j) = 360886343 := by decide
private theorem lowerTwo_row_2839 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2839 j) = 360992549 := by decide
private theorem lowerTwo_row_2840 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2840 j) = 361332513 := by decide
private theorem lowerTwo_row_2841 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2841 j) = 361762405 := by decide
private theorem lowerTwo_row_2842 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2842 j) = 362144566 := by decide
private theorem lowerTwo_row_2843 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2843 j) = 362210988 := by decide
private theorem lowerTwo_row_2844 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2844 j) = 362918396 := by decide
private theorem lowerTwo_row_2845 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2845 j) = 363026990 := by decide
private theorem lowerTwo_row_2846 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2846 j) = 363369452 := by decide
private theorem lowerTwo_row_2847 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2847 j) = 363804843 := by decide
private theorem lowerTwo_row_2848 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2848 j) = 364189518 := by decide
private theorem lowerTwo_row_2849 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2849 j) = 364258304 := by decide
private theorem lowerTwo_row_2850 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2850 j) = 364971377 := by decide
private theorem lowerTwo_row_2851 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2851 j) = 365082415 := by decide
private theorem lowerTwo_row_2852 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2852 j) = 365427346 := by decide
private theorem lowerTwo_row_2853 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2853 j) = 365868307 := by decide
private theorem lowerTwo_row_2854 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2854 j) = 366255517 := by decide
private theorem lowerTwo_row_2855 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2855 j) = 366326769 := by decide
private theorem lowerTwo_row_2856 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2856 j) = 367045533 := by decide
private theorem lowerTwo_row_2857 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2857 j) = 367159013 := by decide
private theorem lowerTwo_row_2858 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2858 j) = 367506505 := by decide
private theorem lowerTwo_row_2859 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2859 j) = 367953088 := by decide
private theorem lowerTwo_row_2860 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2860 j) = 368342881 := by decide
private theorem lowerTwo_row_2861 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2861 j) = 368416584 := by decide
private theorem lowerTwo_row_2862 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2862 j) = 369141129 := by decide
private theorem lowerTwo_row_2863 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2863 j) = 369257079 := by decide
private theorem lowerTwo_row_2864 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2864 j) = 369607155 := by decide
private theorem lowerTwo_row_2865 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2865 j) = 370059421 := by decide
private theorem lowerTwo_row_2866 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2866 j) = 370451822 := by decide
private theorem lowerTwo_row_2867 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2867 j) = 370528046 := by decide
private theorem lowerTwo_row_2868 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2868 j) = 371258361 := by decide
private theorem lowerTwo_row_2869 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2869 j) = 371376828 := by decide
private theorem lowerTwo_row_2870 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2870 j) = 371729542 := by decide
private theorem lowerTwo_row_2871 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2871 j) = 372187525 := by decide
private theorem lowerTwo_row_2872 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2872 j) = 372582600 := by decide
private theorem lowerTwo_row_2873 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2873 j) = 372661326 := by decide
private theorem lowerTwo_row_2874 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2874 j) = 373397557 := by decide
private theorem lowerTwo_row_2875 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2875 j) = 373518583 := by decide
private theorem lowerTwo_row_2876 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2876 j) = 373873944 := by decide
private theorem lowerTwo_row_2877 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2877 j) = 374337778 := by decide
private theorem lowerTwo_row_2878 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2878 j) = 374735491 := by decide
private theorem lowerTwo_row_2879 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2879 j) = 374816775 := by decide
private theorem lowerTwo_row_2880 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2880 j) = 375558959 := by decide
private theorem lowerTwo_row_2881 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2881 j) = 375682617 := by decide
private theorem lowerTwo_row_2882 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2882 j) = 376040622 := by decide
private theorem lowerTwo_row_2883 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2883 j) = 376510352 := by decide
private theorem lowerTwo_row_2884 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2884 j) = 376910775 := by decide
private theorem lowerTwo_row_2885 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2885 j) = 376994619 := by decide
private theorem lowerTwo_row_2886 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2886 j) = 377742876 := by decide
private theorem lowerTwo_row_2887 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2887 j) = 377869129 := by decide
private theorem lowerTwo_row_2888 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2888 j) = 378229835 := by decide
private theorem lowerTwo_row_2889 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2889 j) = 378705578 := by decide
private theorem lowerTwo_row_2890 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2890 j) = 379108688 := by decide
private theorem lowerTwo_row_2891 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2891 j) = 379195179 := by decide
private theorem lowerTwo_row_2892 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2892 j) = 379949527 := by decide
private theorem lowerTwo_row_2893 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2893 j) = 380078410 := by decide
private theorem lowerTwo_row_2894 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2894 j) = 380441888 := by decide
private theorem lowerTwo_row_2895 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2895 j) = 380923626 := by decide
private theorem lowerTwo_row_2896 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2896 j) = 381329549 := by decide
private theorem lowerTwo_row_2897 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2897 j) = 381418676 := by decide
private theorem lowerTwo_row_2898 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2898 j) = 382179252 := by decide
private theorem lowerTwo_row_2899 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2899 j) = 382310760 := by decide
private theorem lowerTwo_row_2900 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2900 j) = 382676999 := by decide
private theorem lowerTwo_row_2901 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2901 j) = 383164770 := by decide
private theorem lowerTwo_row_2902 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2902 j) = 383573363 := by decide
private theorem lowerTwo_row_2903 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2903 j) = 383665121 := by decide
private theorem lowerTwo_row_2904 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2904 j) = 384431609 := by decide
private theorem lowerTwo_row_2905 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2905 j) = 384565742 := by decide
private theorem lowerTwo_row_2906 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2906 j) = 384934617 := by decide
private theorem lowerTwo_row_2907 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2907 j) = 385428205 := by decide
private theorem lowerTwo_row_2908 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2908 j) = 385839539 := by decide
private theorem lowerTwo_row_2909 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2909 j) = 385933867 := by decide
private theorem lowerTwo_row_2910 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2910 j) = 386706320 := by decide
private theorem lowerTwo_row_2911 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2911 j) = 386843062 := by decide
private theorem lowerTwo_row_2912 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2912 j) = 387214648 := by decide
private theorem lowerTwo_row_2913 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2913 j) = 387714145 := by decide
private theorem lowerTwo_row_2914 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2914 j) = 388128229 := by decide
private theorem lowerTwo_row_2915 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2915 j) = 388225136 := by decide
private theorem lowerTwo_row_2916 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2916 j) = 389003692 := by decide
private theorem lowerTwo_row_2917 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2917 j) = 389143068 := by decide
private theorem lowerTwo_row_2918 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2918 j) = 389517379 := by decide
private theorem lowerTwo_row_2919 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2919 j) = 390022871 := by decide
private theorem lowerTwo_row_2920 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2920 j) = 390439743 := by decide
private theorem lowerTwo_row_2921 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2921 j) = 390539255 := by decide
private theorem lowerTwo_row_2922 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2922 j) = 391323946 := by decide
private theorem lowerTwo_row_2923 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2923 j) = 391466014 := by decide
private theorem lowerTwo_row_2924 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2924 j) = 391843091 := by decide
private theorem lowerTwo_row_2925 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2925 j) = 392354659 := by decide
private theorem lowerTwo_row_2926 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2926 j) = 392774312 := by decide
private theorem lowerTwo_row_2927 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2927 j) = 392876521 := by decide
private theorem lowerTwo_row_2928 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2928 j) = 393667442 := by decide
private theorem lowerTwo_row_2929 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2929 j) = 393812189 := by decide
private theorem lowerTwo_row_2930 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2930 j) = 394192087 := by decide
private theorem lowerTwo_row_2931 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2931 j) = 394709780 := by decide
private theorem lowerTwo_row_2932 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2932 j) = 395132266 := by decide
private theorem lowerTwo_row_2933 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2933 j) = 395237196 := by decide
private theorem lowerTwo_row_2934 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2934 j) = 396034366 := by decide
private theorem lowerTwo_row_2935 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2935 j) = 396181863 := by decide
private theorem lowerTwo_row_2936 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2936 j) = 396564640 := by decide
private theorem lowerTwo_row_2937 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2937 j) = 397088541 := by decide
private theorem lowerTwo_row_2938 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2938 j) = 397513872 := by decide
private theorem lowerTwo_row_2939 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2939 j) = 397621596 := by decide
private theorem lowerTwo_row_2940 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2940 j) = 398425136 := by decide
private theorem lowerTwo_row_2941 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2941 j) = 398575408 := by decide
private theorem lowerTwo_row_2942 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2942 j) = 398961050 := by decide
private theorem lowerTwo_row_2943 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2943 j) = 399491218 := by decide
private theorem lowerTwo_row_2944 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2944 j) = 399919487 := by decide
private theorem lowerTwo_row_2945 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2945 j) = 400029971 := by decide
private theorem lowerTwo_row_2946 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2946 j) = 400839943 := by decide
private theorem lowerTwo_row_2947 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2947 j) = 400993034 := by decide
private theorem lowerTwo_row_2948 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2948 j) = 401381575 := by decide
private theorem lowerTwo_row_2949 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2949 j) = 401918162 := by decide
private theorem lowerTwo_row_2950 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2950 j) = 402349352 := by decide
private theorem lowerTwo_row_2951 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2951 j) = 402462648 := by decide
private theorem lowerTwo_row_2952 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2952 j) = 403279185 := by decide
private theorem lowerTwo_row_2953 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2953 j) = 403435110 := by decide
private theorem lowerTwo_row_2954 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2954 j) = 403826630 := by decide
private theorem lowerTwo_row_2955 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2955 j) = 404369629 := by decide
private theorem lowerTwo_row_2956 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2956 j) = 404803835 := by decide
private theorem lowerTwo_row_2957 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2957 j) = 404919960 := by decide
private theorem lowerTwo_row_2958 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2958 j) = 405743090 := by decide
private theorem lowerTwo_row_2959 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2959 j) = 405901897 := by decide
private theorem lowerTwo_row_2960 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2960 j) = 406296323 := by decide
private theorem lowerTwo_row_2961 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2961 j) = 406845707 := by decide
private theorem lowerTwo_row_2962 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2962 j) = 407282839 := by decide
private theorem lowerTwo_row_2963 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2963 j) = 407401775 := by decide
private theorem lowerTwo_row_2964 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2964 j) = 408231260 := by decide
private theorem lowerTwo_row_2965 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2965 j) = 408392838 := by decide
private theorem lowerTwo_row_2966 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2966 j) = 408790209 := by decide
private theorem lowerTwo_row_2967 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2967 j) = 409345865 := by decide
private theorem lowerTwo_row_2968 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2968 j) = 409785890 := by decide
private theorem lowerTwo_row_2969 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2969 j) = 409907646 := by decide
private theorem lowerTwo_row_2970 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2970 j) = 410743558 := by decide
private theorem lowerTwo_row_2971 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2971 j) = 410907952 := by decide
private theorem lowerTwo_row_2972 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2972 j) = 411308277 := by decide
private theorem lowerTwo_row_2973 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2973 j) = 411870254 := by decide
private theorem lowerTwo_row_2974 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2974 j) = 412313284 := by decide
private theorem lowerTwo_row_2975 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2975 j) = 412437864 := by decide
private theorem lowerTwo_row_2976 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2976 j) = 413280283 := by decide
private theorem lowerTwo_row_2977 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2977 j) = 413447580 := by decide
private theorem lowerTwo_row_2978 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2978 j) = 413850833 := by decide
private theorem lowerTwo_row_2979 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2979 j) = 414419262 := by decide
private theorem lowerTwo_row_2980 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2980 j) = 414865334 := by decide
private theorem lowerTwo_row_2981 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2981 j) = 414992770 := by decide
private theorem lowerTwo_row_2982 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2982 j) = 415841783 := by decide
private theorem lowerTwo_row_2983 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2983 j) = 416011984 := by decide
private theorem lowerTwo_row_2984 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2984 j) = 416418261 := by decide
private theorem lowerTwo_row_2985 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2985 j) = 416993213 := by decide
private theorem lowerTwo_row_2986 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2986 j) = 417442308 := by decide
private theorem lowerTwo_row_2987 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2987 j) = 417572647 := by decide
private theorem lowerTwo_row_2988 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2988 j) = 418428380 := by decide
private theorem lowerTwo_row_2989 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2989 j) = 418601500 := by decide
private theorem lowerTwo_row_2990 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2990 j) = 419010842 := by decide
private theorem lowerTwo_row_2991 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2991 j) = 419592387 := by decide
private theorem lowerTwo_row_2992 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2992 j) = 420044578 := by decide
private theorem lowerTwo_row_2993 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2993 j) = 420177840 := by decide
private theorem lowerTwo_row_2994 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2994 j) = 421040359 := by decide
private theorem lowerTwo_row_2995 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2995 j) = 421216477 := by decide
private theorem lowerTwo_row_2996 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2996 j) = 421628902 := by decide
private theorem lowerTwo_row_2997 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2997 j) = 422217129 := by decide
private theorem lowerTwo_row_2998 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2998 j) = 422672446 := by decide
private theorem lowerTwo_row_2999 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2999 j) = 422808717 := by decide
private theorem lowerTwo_row_3000 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3000 j) = 423678079 := by decide
private theorem lowerTwo_row_3001 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3001 j) = 423857197 := by decide
private theorem lowerTwo_row_3002 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3002 j) = 424272786 := by decide
private theorem lowerTwo_row_3003 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3003 j) = 424867812 := by decide
private theorem lowerTwo_row_3004 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3004 j) = 425326267 := by decide
private theorem lowerTwo_row_3005 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3005 j) = 425465591 := by decide
private theorem lowerTwo_row_3006 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3006 j) = 426341903 := by decide
private theorem lowerTwo_row_3007 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3007 j) = 426524069 := by decide
private theorem lowerTwo_row_3008 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3008 j) = 426942832 := by decide
private theorem lowerTwo_row_3009 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3009 j) = 427544681 := by decide
private theorem lowerTwo_row_3010 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3010 j) = 428006387 := by decide
private theorem lowerTwo_row_3011 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3011 j) = 428148771 := by decide
private theorem lowerTwo_row_3012 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3012 j) = 429032086 := by decide
private theorem lowerTwo_row_3013 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3013 j) = 429217384 := by decide
private theorem lowerTwo_row_3014 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3014 j) = 429639345 := by decide
private theorem lowerTwo_row_3015 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3015 j) = 430248006 := by decide
private theorem lowerTwo_row_3016 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3016 j) = 430712901 := by decide
private theorem lowerTwo_row_3017 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3017 j) = 430858334 := by decide
private theorem lowerTwo_row_3018 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3018 j) = 431748472 := by decide
private theorem lowerTwo_row_3019 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3019 j) = 431936785 := by decide
private theorem lowerTwo_row_3020 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3020 j) = 432361871 := by decide
private theorem lowerTwo_row_3021 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3021 j) = 432977309 := by decide
private theorem lowerTwo_row_3022 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3022 j) = 433445364 := by decide
private theorem lowerTwo_row_3023 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3023 j) = 433593757 := by decide
private theorem lowerTwo_row_3024 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3024 j) = 434490842 := by decide
private theorem lowerTwo_row_3025 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3025 j) = 434682196 := by decide
private theorem lowerTwo_row_3026 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3026 j) = 435110441 := by decide
private theorem lowerTwo_row_3027 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3027 j) = 435732709 := by decide
private theorem lowerTwo_row_3028 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3028 j) = 436203944 := by decide
private theorem lowerTwo_row_3029 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3029 j) = 436355386 := by decide
private theorem lowerTwo_row_3030 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3030 j) = 437259547 := by decide
private theorem lowerTwo_row_3031 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3031 j) = 437453967 := by decide
private theorem lowerTwo_row_3032 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3032 j) = 437885427 := by decide
private theorem lowerTwo_row_3033 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3033 j) = 438514598 := by decide
private theorem lowerTwo_row_3034 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3034 j) = 438989072 := by decide
private theorem lowerTwo_row_3035 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3035 j) = 439143643 := by decide
private theorem lowerTwo_row_3036 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3036 j) = 440054848 := by decide
private theorem lowerTwo_row_3037 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3037 j) = 440252405 := by decide
private theorem lowerTwo_row_3038 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3038 j) = 440687159 := by decide
private theorem lowerTwo_row_3039 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3039 j) = 441323303 := by decide
private theorem lowerTwo_row_3040 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3040 j) = 441801069 := by decide
private theorem lowerTwo_row_3041 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3041 j) = 441958810 := by decide
private theorem lowerTwo_row_3042 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3042 j) = 442877161 := by decide
private theorem lowerTwo_row_3043 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3043 j) = 443077938 := by decide
private theorem lowerTwo_row_3044 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3044 j) = 443515933 := by decide
private theorem lowerTwo_row_3045 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3045 j) = 444159171 := by decide
private theorem lowerTwo_row_3046 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3046 j) = 444640334 := by decide
private theorem lowerTwo_row_3047 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3047 j) = 444801259 := by decide
private theorem lowerTwo_row_3048 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3048 j) = 445726843 := by decide
private theorem lowerTwo_row_3049 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3049 j) = 445930840 := by decide
private theorem lowerTwo_row_3050 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3050 j) = 446372247 := by decide
private theorem lowerTwo_row_3051 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3051 j) = 447022647 := by decide
private theorem lowerTwo_row_3052 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3052 j) = 447507176 := by decide
private theorem lowerTwo_row_3053 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3053 j) = 447671320 := by decide
private theorem lowerTwo_row_3054 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3054 j) = 448604301 := by decide
private theorem lowerTwo_row_3055 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3055 j) = 448811585 := by decide
private theorem lowerTwo_row_3056 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3056 j) = 449256336 := by decide
private theorem lowerTwo_row_3057 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3057 j) = 449914048 := by decide
private theorem lowerTwo_row_3058 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3058 j) = 450401988 := by decide
private theorem lowerTwo_row_3059 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3059 j) = 450569430 := by decide
private theorem lowerTwo_row_3060 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3060 j) = 451509879 := by decide
private theorem lowerTwo_row_3061 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3061 j) = 451720473 := by decide
private theorem lowerTwo_row_3062 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3062 j) = 452168636 := by decide
private theorem lowerTwo_row_3063 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3063 j) = 452833733 := by decide
private theorem lowerTwo_row_3064 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3064 j) = 453325141 := by decide
private theorem lowerTwo_row_3065 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3065 j) = 453495876 := by decide
private theorem lowerTwo_row_3066 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3066 j) = 454443782 := by decide
private theorem lowerTwo_row_3067 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3067 j) = 454657663 := by decide
private theorem lowerTwo_row_3068 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3068 j) = 455109246 := by decide
private theorem lowerTwo_row_3069 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3069 j) = 455781561 := by decide
private theorem lowerTwo_row_3070 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3070 j) = 456276363 := by decide
private theorem lowerTwo_row_3071 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3071 j) = 456450348 := by decide
private theorem lowerTwo_row_3072 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3072 j) = 457405593 := by decide
private theorem lowerTwo_row_3073 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3073 j) = 457622738 := by decide
private theorem lowerTwo_row_3074 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3074 j) = 458077770 := by decide
private theorem lowerTwo_row_3075 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3075 j) = 458757311 := by decide
private theorem lowerTwo_row_3076 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3076 j) = 459255560 := by decide
private theorem lowerTwo_row_3077 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3077 j) = 459432839 := by decide
private theorem lowerTwo_row_3078 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3078 j) = 460395530 := by decide
private theorem lowerTwo_row_3079 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3079 j) = 460616020 := by decide
private theorem lowerTwo_row_3080 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3080 j) = 461074502 := by decide
private theorem lowerTwo_row_3081 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3081 j) = 461761416 := by decide
private theorem lowerTwo_row_3082 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3082 j) = 462263166 := by decide
private theorem lowerTwo_row_3083 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3083 j) = 462443812 := by decide
private theorem lowerTwo_row_3084 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3084 j) = 463414000 := by decide
private theorem lowerTwo_row_3085 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3085 j) = 463637912 := by decide
private theorem lowerTwo_row_3086 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3086 j) = 464099861 := by decide
private theorem lowerTwo_row_3087 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3087 j) = 464794240 := by decide
private theorem lowerTwo_row_3088 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3088 j) = 465299547 := by decide
private theorem lowerTwo_row_3089 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3089 j) = 465483534 := by decide
private theorem lowerTwo_row_3090 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3090 j) = 466461448 := by decide
private theorem lowerTwo_row_3091 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3091 j) = 466688758 := by decide
private theorem lowerTwo_row_3092 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3092 j) = 467154248 := by decide
private theorem lowerTwo_row_3093 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3093 j) = 467856206 := by decide
private theorem lowerTwo_row_3094 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3094 j) = 468365108 := by decide
private theorem lowerTwo_row_3095 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3095 j) = 468552500 := by decide
private theorem lowerTwo_row_3096 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3096 j) = 469538203 := by decide
private theorem lowerTwo_row_3097 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3097 j) = 469768979 := by decide
private theorem lowerTwo_row_3098 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3098 j) = 470238067 := by decide
private theorem lowerTwo_row_3099 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3099 j) = 470947718 := by decide
private theorem lowerTwo_row_3100 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3100 j) = 471460258 := by decide
private theorem lowerTwo_row_3101 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3101 j) = 471651137 := by decide
private theorem lowerTwo_row_3102 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3102 j) = 472644682 := by decide
private theorem lowerTwo_row_3103 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3103 j) = 472878973 := by decide
private theorem lowerTwo_row_3104 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3104 j) = 473351751 := by decide
private theorem lowerTwo_row_3105 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3105 j) = 474069142 := by decide
private theorem lowerTwo_row_3106 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3106 j) = 474585366 := by decide
private theorem lowerTwo_row_3107 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3107 j) = 474779797 := by decide
private theorem lowerTwo_row_3108 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3108 j) = 475781360 := by decide
private theorem lowerTwo_row_3109 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3109 j) = 476019192 := by decide
private theorem lowerTwo_row_3110 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3110 j) = 476495678 := by decide
private theorem lowerTwo_row_3111 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3111 j) = 477220986 := by decide
private theorem lowerTwo_row_3112 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3112 j) = 477740916 := by decide
private theorem lowerTwo_row_3113 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3113 j) = 477938933 := by decide
private theorem lowerTwo_row_3114 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3114 j) = 478948562 := by decide
private theorem lowerTwo_row_3115 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3115 j) = 479190040 := by decide
private theorem lowerTwo_row_3116 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3116 j) = 479670251 := by decide
private theorem lowerTwo_row_3117 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3117 j) = 480403537 := by decide
private theorem lowerTwo_row_3118 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3118 j) = 480927311 := by decide
private theorem lowerTwo_row_3119 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3119 j) = 481128975 := by decide
private theorem lowerTwo_row_3120 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3120 j) = 482146760 := by decide
private theorem lowerTwo_row_3121 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3121 j) = 482391953 := by decide
private theorem lowerTwo_row_3122 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3122 j) = 482875959 := by decide
private theorem lowerTwo_row_3123 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3123 j) = 483617361 := by decide
private theorem lowerTwo_row_3124 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3124 j) = 484144991 := by decide
private theorem lowerTwo_row_3125 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3125 j) = 484350289 := by decide
private theorem lowerTwo_row_3126 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3126 j) = 485376308 := by decide
private theorem lowerTwo_row_3127 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3127 j) = 485625111 := by decide
private theorem lowerTwo_row_3128 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3128 j) = 486112888 := by decide
private theorem lowerTwo_row_3129 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3129 j) = 486862164 := by decide
private theorem lowerTwo_row_3130 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3130 j) = 487393479 := by decide
private theorem lowerTwo_row_3131 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3131 j) = 487602341 := by decide
private theorem lowerTwo_row_3132 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3132 j) = 488636321 := by decide
private theorem lowerTwo_row_3133 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3133 j) = 488888682 := by decide
private theorem lowerTwo_row_3134 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3134 j) = 489380177 := by decide
private theorem lowerTwo_row_3135 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3135 j) = 489544430 := by decide
private theorem lowerTwo_row_3136 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3136 j) = 488893104 := by decide
private theorem lowerTwo_row_3137 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3137 j) = 487918414 := by decide
private theorem lowerTwo_row_3138 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3138 j) = 487772452 := by decide
private theorem lowerTwo_row_3139 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3139 j) = 486839718 := by decide
private theorem lowerTwo_row_3140 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3140 j) = 486145407 := by decide
private theorem lowerTwo_row_3141 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3141 j) = 485720111 := by decide
private theorem lowerTwo_row_3142 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3142 j) = 485067791 := by decide
private theorem lowerTwo_row_3143 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3143 j) = 484091900 := by decide
private theorem lowerTwo_row_3144 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3144 j) = 483949280 := by decide
private theorem lowerTwo_row_3145 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3145 j) = 483015302 := by decide
private theorem lowerTwo_row_3146 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3146 j) = 482319942 := by decide
private theorem lowerTwo_row_3147 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3147 j) = 481897753 := by decide
private theorem lowerTwo_row_3148 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3148 j) = 481244349 := by decide
private theorem lowerTwo_row_3149 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3149 j) = 480267195 := by decide
private theorem lowerTwo_row_3150 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3150 j) = 480127773 := by decide
private theorem lowerTwo_row_3151 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3151 j) = 479192556 := by decide
private theorem lowerTwo_row_3152 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3152 j) = 478495977 := by decide
private theorem lowerTwo_row_3153 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3153 j) = 478076868 := by decide
private theorem lowerTwo_row_3154 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3154 j) = 477422293 := by decide
private theorem lowerTwo_row_3155 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3155 j) = 476443687 := by decide
private theorem lowerTwo_row_3156 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3156 j) = 476307505 := by decide
private theorem lowerTwo_row_3157 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3157 j) = 475370869 := by decide
private theorem lowerTwo_row_3158 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3158 j) = 474672975 := by decide
private theorem lowerTwo_row_3159 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3159 j) = 474256927 := by decide
private theorem lowerTwo_row_3160 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3160 j) = 473601010 := by decide
private theorem lowerTwo_row_3161 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3161 j) = 472620908 := by decide
private theorem lowerTwo_row_3162 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3162 j) = 472487906 := by decide
private theorem lowerTwo_row_3163 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3163 j) = 471549745 := by decide
private theorem lowerTwo_row_3164 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3164 j) = 470850407 := by decide
private theorem lowerTwo_row_3165 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3165 j) = 470437357 := by decide
private theorem lowerTwo_row_3166 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3166 j) = 469780013 := by decide
private theorem lowerTwo_row_3167 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3167 j) = 468798252 := by decide
private theorem lowerTwo_row_3168 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3168 j) = 468668383 := by decide
private theorem lowerTwo_row_3169 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3169 j) = 467728560 := by decide
private theorem lowerTwo_row_3170 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3170 j) = 467027694 := by decide
private theorem lowerTwo_row_3171 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3171 j) = 466617587 := by decide
private theorem lowerTwo_row_3172 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3172 j) = 465958667 := by decide
private theorem lowerTwo_row_3173 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3173 j) = 464975197 := by decide
private theorem lowerTwo_row_3174 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3174 j) = 464848393 := by decide
private theorem lowerTwo_row_3175 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3175 j) = 463906769 := by decide
private theorem lowerTwo_row_3176 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3176 j) = 463204276 := by decide
private theorem lowerTwo_row_3177 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3177 j) = 462797042 := by decide
private theorem lowerTwo_row_3178 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3178 j) = 462136449 := by decide
private theorem lowerTwo_row_3179 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3179 j) = 461149326 := by decide
private theorem lowerTwo_row_3180 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3180 j) = 461020929 := by decide
private theorem lowerTwo_row_3181 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3181 j) = 460070090 := by decide
private theorem lowerTwo_row_3182 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3182 j) = 459355677 := by decide
private theorem lowerTwo_row_3183 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3183 j) = 458938358 := by decide
private theorem lowerTwo_row_3184 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3184 j) = 458260237 := by decide
private theorem lowerTwo_row_3185 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3185 j) = 457254280 := by decide
private theorem lowerTwo_row_3186 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3186 j) = 457111959 := by decide
private theorem lowerTwo_row_3187 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3187 j) = 456142161 := by decide
private theorem lowerTwo_row_3188 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3188 j) = 455408775 := by decide
private theorem lowerTwo_row_3189 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3189 j) = 454977051 := by decide
private theorem lowerTwo_row_3190 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3190 j) = 454279756 := by decide
private theorem lowerTwo_row_3191 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3191 j) = 453254327 := by decide
private theorem lowerTwo_row_3192 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3192 j) = 453097464 := by decide
private theorem lowerTwo_row_3193 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3193 j) = 452107982 := by decide
private theorem lowerTwo_row_3194 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3194 j) = 451354952 := by decide
private theorem lowerTwo_row_3195 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3195 j) = 450908168 := by decide
private theorem lowerTwo_row_3196 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3196 j) = 450190986 := by decide
private theorem lowerTwo_row_3197 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3197 j) = 449145376 := by decide
private theorem lowerTwo_row_3198 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3198 j) = 448973339 := by decide
private theorem lowerTwo_row_3199 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3199 j) = 447963445 := by decide
private theorem lowerTwo_row_3200 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3200 j) = 447190023 := by decide
private theorem lowerTwo_row_3201 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3201 j) = 446727550 := by decide
private theorem lowerTwo_row_3202 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3202 j) = 445989782 := by decide
private theorem lowerTwo_row_3203 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3203 j) = 444923255 := by decide
private theorem lowerTwo_row_3204 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3204 j) = 444735345 := by decide
private theorem lowerTwo_row_3205 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3205 j) = 443704316 := by decide
private theorem lowerTwo_row_3206 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3206 j) = 442909743 := by decide
private theorem lowerTwo_row_3207 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3207 j) = 442430877 := by decide
private theorem lowerTwo_row_3208 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3208 j) = 441671733 := by decide
private theorem lowerTwo_row_3209 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3209 j) = 440583483 := by decide
private theorem lowerTwo_row_3210 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3210 j) = 440379008 := by decide
private theorem lowerTwo_row_3211 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3211 j) = 439326016 := by decide
private theorem lowerTwo_row_3212 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3212 j) = 438509525 := by decide
private theorem lowerTwo_row_3213 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3213 j) = 438013544 := by decide
private theorem lowerTwo_row_3214 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3214 j) = 437232227 := by decide
private theorem lowerTwo_row_3215 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3215 j) = 436121484 := by decide
private theorem lowerTwo_row_3216 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3216 j) = 435899663 := by decide
private theorem lowerTwo_row_3217 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3217 j) = 434823916 := by decide
private theorem lowerTwo_row_3218 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3218 j) = 433984649 := by decide
private theorem lowerTwo_row_3219 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3219 j) = 433470808 := by decide
private theorem lowerTwo_row_3220 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3220 j) = 432666434 := by decide
private theorem lowerTwo_row_3221 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3221 j) = 431532362 := by decide
private theorem lowerTwo_row_3222 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3222 j) = 431292431 := by decide
private theorem lowerTwo_row_3223 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3223 j) = 430193050 := by decide
private theorem lowerTwo_row_3224 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3224 j) = 429330132 := by decide
private theorem lowerTwo_row_3225 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3225 j) = 428797652 := by decide
private theorem lowerTwo_row_3226 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3226 j) = 427969384 := by decide
private theorem lowerTwo_row_3227 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3227 j) = 426811030 := by decide
private theorem lowerTwo_row_3228 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3228 j) = 426637014 := by decide
private theorem lowerTwo_row_3229 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3229 j) = 425638337 := by decide
private theorem lowerTwo_row_3230 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3230 j) = 424916182 := by decide
private theorem lowerTwo_row_3231 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3231 j) = 424526920 := by decide
private theorem lowerTwo_row_3232 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3232 j) = 423791520 := by decide
private theorem lowerTwo_row_3233 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3233 j) = 422765678 := by decide
private theorem lowerTwo_row_3234 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3234 j) = 422642220 := by decide
private theorem lowerTwo_row_3235 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3235 j) = 421602840 := by decide
private theorem lowerTwo_row_3236 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3236 j) = 420839842 := by decide
private theorem lowerTwo_row_3237 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3237 j) = 420414973 := by decide
private theorem lowerTwo_row_3238 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3238 j) = 419638966 := by decide
private theorem lowerTwo_row_3239 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3239 j) = 418572651 := by decide
private theorem lowerTwo_row_3240 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3240 j) = 418414686 := by decide
private theorem lowerTwo_row_3241 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3241 j) = 417335506 := by decide
private theorem lowerTwo_row_3242 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3242 j) = 416533222 := by decide
private theorem lowerTwo_row_3243 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3243 j) = 416074552 := by decide
private theorem lowerTwo_row_3244 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3244 j) = 415259181 := by decide
private theorem lowerTwo_row_3245 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3245 j) = 414153091 := by decide
private theorem lowerTwo_row_3246 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3246 j) = 413960819 := by decide
private theorem lowerTwo_row_3247 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3247 j) = 412841391 := by decide
private theorem lowerTwo_row_3248 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3248 j) = 411998678 := by decide
private theorem lowerTwo_row_3249 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3249 j) = 411504780 := by decide
private theorem lowerTwo_row_3250 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3250 j) = 410648546 := by decide
private theorem lowerTwo_row_3251 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3251 j) = 409501112 := by decide
private theorem lowerTwo_row_3252 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3252 j) = 409273019 := by decide
private theorem lowerTwo_row_3253 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3253 j) = 408111711 := by decide
private theorem lowerTwo_row_3254 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3254 j) = 407227055 := by decide
private theorem lowerTwo_row_3255 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3255 j) = 406696552 := by decide
private theorem lowerTwo_row_3256 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3256 j) = 405798453 := by decide
private theorem lowerTwo_row_3257 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3257 j) = 404609273 := by decide
private theorem lowerTwo_row_3258 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3258 j) = 404345583 := by decide
private theorem lowerTwo_row_3259 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3259 j) = 403142973 := by decide
private theorem lowerTwo_row_3260 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3260 j) = 402217531 := by decide
private theorem lowerTwo_row_3261 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3261 j) = 401651921 := by decide
private theorem lowerTwo_row_3262 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3262 j) = 400712835 := by decide
private theorem lowerTwo_row_3263 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3263 j) = 399482211 := by decide
private theorem lowerTwo_row_3264 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3264 j) = 399182802 := by decide
private theorem lowerTwo_row_3265 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3265 j) = 397938216 := by decide
private theorem lowerTwo_row_3266 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3266 j) = 396970645 := by decide
private theorem lowerTwo_row_3267 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3267 j) = 396368329 := by decide
private theorem lowerTwo_row_3268 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3268 j) = 395386594 := by decide
private theorem lowerTwo_row_3269 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3269 j) = 394112867 := by decide
private theorem lowerTwo_row_3270 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3270 j) = 393776085 := by decide
private theorem lowerTwo_row_3271 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3271 j) = 392487806 := by decide
private theorem lowerTwo_row_3272 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3272 j) = 391476693 := by decide
private theorem lowerTwo_row_3273 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3273 j) = 390836791 := by decide
private theorem lowerTwo_row_3274 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3274 j) = 389811894 := by decide
private theorem lowerTwo_row_3275 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3275 j) = 388495045 := by decide
private theorem lowerTwo_row_3276 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3276 j) = 388121476 := by decide
private theorem lowerTwo_row_3277 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3277 j) = 386790460 := by decide
private theorem lowerTwo_row_3278 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3278 j) = 385736721 := by decide
private theorem lowerTwo_row_3279 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3279 j) = 385059711 := by decide
private theorem lowerTwo_row_3280 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3280 j) = 383991613 := by decide
private theorem lowerTwo_row_3281 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3281 j) = 382630999 := by decide
private theorem lowerTwo_row_3282 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3282 j) = 382219688 := by decide
private theorem lowerTwo_row_3283 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3283 j) = 380844389 := by decide
private theorem lowerTwo_row_3284 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3284 j) = 379746194 := by decide
private theorem lowerTwo_row_3285 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3285 j) = 379030362 := by decide
private theorem lowerTwo_row_3286 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3286 j) = 377917169 := by decide
private theorem lowerTwo_row_3287 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3287 j) = 376511072 := by decide
private theorem lowerTwo_row_3288 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3288 j) = 376060660 := by decide
private theorem lowerTwo_row_3289 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3289 j) = 374640057 := by decide
private theorem lowerTwo_row_3290 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3290 j) = 373496856 := by decide
private theorem lowerTwo_row_3291 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3291 j) = 372742240 := by decide
private theorem lowerTwo_row_3292 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3292 j) = 371584345 := by decide
private theorem lowerTwo_row_3293 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3293 j) = 370133475 := by decide
private theorem lowerTwo_row_3294 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3294 j) = 369644468 := by decide
private theorem lowerTwo_row_3295 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3295 j) = 368178515 := by decide
private theorem lowerTwo_row_3296 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3296 j) = 366989850 := by decide
private theorem lowerTwo_row_3297 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3297 j) = 366195549 := by decide
private theorem lowerTwo_row_3298 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3298 j) = 364991513 := by decide
private theorem lowerTwo_row_3299 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3299 j) = 363493987 := by decide
private theorem lowerTwo_row_3300 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3300 j) = 362964529 := by decide
private theorem lowerTwo_row_3301 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3301 j) = 361451253 := by decide
private theorem lowerTwo_row_3302 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3302 j) = 360215234 := by decide
private theorem lowerTwo_row_3303 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3303 j) = 359379928 := by decide
private theorem lowerTwo_row_3304 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3304 j) = 358128737 := by decide
private theorem lowerTwo_row_3305 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3305 j) = 356583956 := by decide
private theorem lowerTwo_row_3306 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3306 j) = 356013970 := by decide
private theorem lowerTwo_row_3307 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3307 j) = 354453627 := by decide
private theorem lowerTwo_row_3308 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3308 j) = 353170679 := by decide
private theorem lowerTwo_row_3309 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3309 j) = 352294406 := by decide
private theorem lowerTwo_row_3310 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3310 j) = 350995608 := by decide
private theorem lowerTwo_row_3311 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3311 j) = 349402681 := by decide
private theorem lowerTwo_row_3312 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3312 j) = 348790918 := by decide
private theorem lowerTwo_row_3313 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3313 j) = 347181765 := by decide
private theorem lowerTwo_row_3314 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3314 j) = 345849769 := by decide
private theorem lowerTwo_row_3315 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3315 j) = 344930517 := by decide
private theorem lowerTwo_row_3316 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3316 j) = 343582171 := by decide
private theorem lowerTwo_row_3317 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3317 j) = 341939629 := by decide
private theorem lowerTwo_row_3318 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3318 j) = 341285063 := by decide
private theorem lowerTwo_row_3319 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3319 j) = 339626300 := by decide
private theorem lowerTwo_row_3320 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3320 j) = 338244949 := by decide
private theorem lowerTwo_row_3321 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3321 j) = 337282910 := by decide
private theorem lowerTwo_row_3322 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3322 j) = 335885103 := by decide
private theorem lowerTwo_row_3323 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3323 j) = 334192433 := by decide
private theorem lowerTwo_row_3324 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3324 j) = 333494451 := by decide
private theorem lowerTwo_row_3325 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3325 j) = 331784853 := by decide
private theorem lowerTwo_row_3326 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3326 j) = 330352502 := by decide
private theorem lowerTwo_row_3327 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3327 j) = 329345742 := by decide
private theorem lowerTwo_row_3328 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3328 j) = 327896124 := by decide
private theorem lowerTwo_row_3329 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3329 j) = 326151118 := by decide
private theorem lowerTwo_row_3330 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3330 j) = 325407415 := by decide
private theorem lowerTwo_row_3331 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3331 j) = 323644696 := by decide
private theorem lowerTwo_row_3332 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3332 j) = 322158994 := by decide
private theorem lowerTwo_row_3333 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3333 j) = 321105736 := by decide
private theorem lowerTwo_row_3334 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3334 j) = 319603131 := by decide
private theorem lowerTwo_row_3335 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3335 j) = 317805178 := by decide
private theorem lowerTwo_row_3336 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3336 j) = 317015902 := by decide
private theorem lowerTwo_row_3337 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3337 j) = 315200683 := by decide
private theorem lowerTwo_row_3338 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3338 j) = 313662863 := by decide
private theorem lowerTwo_row_3339 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3339 j) = 312564049 := by decide
private theorem lowerTwo_row_3340 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3340 j) = 311008635 := by decide
private theorem lowerTwo_row_3341 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3341 j) = 309157247 := by decide
private theorem lowerTwo_row_3342 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3342 j) = 308321455 := by decide
private theorem lowerTwo_row_3343 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3343 j) = 306451983 := by decide
private theorem lowerTwo_row_3344 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3344 j) = 304859691 := by decide
private theorem lowerTwo_row_3345 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3345 j) = 303712931 := by decide
private theorem lowerTwo_row_3346 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3346 j) = 302102209 := by decide
private theorem lowerTwo_row_3347 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3347 j) = 300194856 := by decide
private theorem lowerTwo_row_3348 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3348 j) = 299310068 := by decide
private theorem lowerTwo_row_3349 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3349 j) = 297383773 := by decide
private theorem lowerTwo_row_3350 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3350 j) = 295734364 := by decide
private theorem lowerTwo_row_3351 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3351 j) = 294537150 := by decide
private theorem lowerTwo_row_3352 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3352 j) = 292868418 := by decide
private theorem lowerTwo_row_3353 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3353 j) = 290902394 := by decide
private theorem lowerTwo_row_3354 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3354 j) = 289965991 := by decide
private theorem lowerTwo_row_3355 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3355 j) = 287980096 := by decide
private theorem lowerTwo_row_3356 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3356 j) = 286270804 := by decide
private theorem lowerTwo_row_3357 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3357 j) = 285020410 := by decide
private theorem lowerTwo_row_3358 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3358 j) = 283290843 := by decide
private theorem lowerTwo_row_3359 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3359 j) = 281263286 := by decide
private theorem lowerTwo_row_3360 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3360 j) = 280272494 := by decide
private theorem lowerTwo_row_3361 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3361 j) = 278224081 := by decide
private theorem lowerTwo_row_3362 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3362 j) = 276451961 := by decide
private theorem lowerTwo_row_3363 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3363 j) = 275145515 := by decide
private theorem lowerTwo_row_3364 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3364 j) = 273352050 := by decide
private theorem lowerTwo_row_3365 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3365 j) = 271259923 := by decide
private theorem lowerTwo_row_3366 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3366 j) = 270211783 := by decide
private theorem lowerTwo_row_3367 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3367 j) = 268097732 := by decide
private theorem lowerTwo_row_3368 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3368 j) = 266259585 := by decide
private theorem lowerTwo_row_3369 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3369 j) = 264894079 := by decide
private theorem lowerTwo_row_3370 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3370 j) = 263033498 := by decide
private theorem lowerTwo_row_3371 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3371 j) = 260873536 := by decide
private theorem lowerTwo_row_3372 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3372 j) = 259764893 := by decide
private theorem lowerTwo_row_3373 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3373 j) = 257581856 := by decide
private theorem lowerTwo_row_3374 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3374 j) = 255674377 := by decide
private theorem lowerTwo_row_3375 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3375 j) = 254246481 := by decide
private theorem lowerTwo_row_3376 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3376 j) = 252315425 := by decide
private theorem lowerTwo_row_3377 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3377 j) = 250084142 := by decide
private theorem lowerTwo_row_3378 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3378 j) = 248911612 := by decide
private theorem lowerTwo_row_3379 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3379 j) = 246656072 := by decide
private theorem lowerTwo_row_3380 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3380 j) = 244675649 := by decide
private theorem lowerTwo_row_3381 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3381 j) = 243181908 := by decide
private theorem lowerTwo_row_3382 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3382 j) = 241176689 := by decide
private theorem lowerTwo_row_3383 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3383 j) = 238870414 := by decide
private theorem lowerTwo_row_3384 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3384 j) = 237630389 := by decide
private theorem lowerTwo_row_3385 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3385 j) = 235298565 := by decide
private theorem lowerTwo_row_3386 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3386 j) = 233241429 := by decide
private theorem lowerTwo_row_3387 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3387 j) = 231678111 := by decide
private theorem lowerTwo_row_3388 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3388 j) = 229594805 := by decide
private theorem lowerTwo_row_3389 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3389 j) = 227209584 := by decide
private theorem lowerTwo_row_3390 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3390 j) = 225898236 := by decide
private theorem lowerTwo_row_3391 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3391 j) = 223486092 := by decide
private theorem lowerTwo_row_3392 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3392 j) = 221348119 := by decide
private theorem lowerTwo_row_3393 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3393 j) = 219711242 := by decide
private theorem lowerTwo_row_3394 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3394 j) = 217545720 := by decide
private theorem lowerTwo_row_3395 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3395 j) = 215077335 := by decide
private theorem lowerTwo_row_3396 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3396 j) = 213690521 := by decide
private theorem lowerTwo_row_3397 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3397 j) = 211193759 := by decide
private theorem lowerTwo_row_3398 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3398 j) = 208970622 := by decide
private theorem lowerTwo_row_3399 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3399 j) = 207255916 := by decide
private theorem lowerTwo_row_3400 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3400 j) = 205003706 := by decide
private theorem lowerTwo_row_3401 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3401 j) = 202447658 := by decide
private theorem lowerTwo_row_3402 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3402 j) = 200980972 := by decide
private theorem lowerTwo_row_3403 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3403 j) = 198394996 := by decide
private theorem lowerTwo_row_3404 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3404 j) = 196082008 := by decide
private theorem lowerTwo_row_3405 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3405 j) = 194284888 := by decide
private theorem lowerTwo_row_3406 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3406 j) = 191941224 := by decide
private theorem lowerTwo_row_3407 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3407 j) = 189292665 := by decide
private theorem lowerTwo_row_3408 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3408 j) = 187741371 := by decide
private theorem lowerTwo_row_3409 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3409 j) = 185061210 := by decide
private theorem lowerTwo_row_3410 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3410 j) = 182653421 := by decide
private theorem lowerTwo_row_3411 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3411 j) = 180768983 := by decide
private theorem lowerTwo_row_3412 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3412 j) = 178328724 := by decide
private theorem lowerTwo_row_3413 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3413 j) = 174751480 := by decide
private theorem lowerTwo_row_3414 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3414 j) = 173108206 := by decide
private theorem lowerTwo_row_3415 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3415 j) = 172834361 := by decide
private theorem lowerTwo_row_3416 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3416 j) = 172849582 := by decide
private theorem lowerTwo_row_3417 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3417 j) = 172575672 := by decide
private theorem lowerTwo_row_3418 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3418 j) = 172590919 := by decide
private theorem lowerTwo_row_3419 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3419 j) = 172316951 := by decide
private theorem lowerTwo_row_3420 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3420 j) = 172332208 := by decide
private theorem lowerTwo_row_3421 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3421 j) = 172058191 := by decide
private theorem lowerTwo_row_3422 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3422 j) = 172073470 := by decide
private theorem lowerTwo_row_3423 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3423 j) = 171799415 := by decide
private theorem lowerTwo_row_3424 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3424 j) = 171814688 := by decide
private theorem lowerTwo_row_3425 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3425 j) = 171540572 := by decide
private theorem lowerTwo_row_3426 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3426 j) = 171555872 := by decide
private theorem lowerTwo_row_3427 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3427 j) = 171281689 := by decide
private theorem lowerTwo_row_3428 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3428 j) = 171296988 := by decide
private theorem lowerTwo_row_3429 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3429 j) = 171022780 := by decide
private theorem lowerTwo_row_3430 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3430 j) = 171038104 := by decide
private theorem lowerTwo_row_3431 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3431 j) = 170763824 := by decide
private theorem lowerTwo_row_3432 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3432 j) = 170779164 := by decide
private theorem lowerTwo_row_3433 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3433 j) = 170504835 := by decide
private theorem lowerTwo_row_3434 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3434 j) = 170520181 := by decide
private theorem lowerTwo_row_3435 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3435 j) = 170245789 := by decide
private theorem lowerTwo_row_3436 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3436 j) = 170261166 := by decide
private theorem lowerTwo_row_3437 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3437 j) = 169986729 := by decide
private theorem lowerTwo_row_3438 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3438 j) = 170002100 := by decide
private theorem lowerTwo_row_3439 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3439 j) = 169727602 := by decide
private theorem lowerTwo_row_3440 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3440 j) = 169742990 := by decide
private theorem lowerTwo_row_3441 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3441 j) = 169468460 := by decide
private theorem lowerTwo_row_3442 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3442 j) = 169483847 := by decide
private theorem lowerTwo_row_3443 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3443 j) = 169209255 := by decide
private theorem lowerTwo_row_3444 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3444 j) = 169224655 := by decide
private theorem lowerTwo_row_3445 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3445 j) = 168950004 := by decide
private theorem lowerTwo_row_3446 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3446 j) = 168965438 := by decide
private theorem lowerTwo_row_3447 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3447 j) = 168690720 := by decide
private theorem lowerTwo_row_3448 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3448 j) = 168706164 := by decide
private theorem lowerTwo_row_3449 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3449 j) = 168431384 := by decide
private theorem lowerTwo_row_3450 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3450 j) = 168446833 := by decide
private theorem lowerTwo_row_3451 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3451 j) = 168172010 := by decide
private theorem lowerTwo_row_3452 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3452 j) = 168187476 := by decide
private theorem lowerTwo_row_3453 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3453 j) = 167912604 := by decide
private theorem lowerTwo_row_3454 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3454 j) = 167928077 := by decide
private theorem lowerTwo_row_3455 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3455 j) = 167653134 := by decide
private theorem lowerTwo_row_3456 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3456 j) = 167668633 := by decide
private theorem lowerTwo_row_3457 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3457 j) = 167393626 := by decide
private theorem lowerTwo_row_3458 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3458 j) = 167409139 := by decide
private theorem lowerTwo_row_3459 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3459 j) = 167134072 := by decide
private theorem lowerTwo_row_3460 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3460 j) = 167149586 := by decide
private theorem lowerTwo_row_3461 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3461 j) = 166874490 := by decide
private theorem lowerTwo_row_3462 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3462 j) = 166890019 := by decide
private theorem lowerTwo_row_3463 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3463 j) = 166614829 := by decide
private theorem lowerTwo_row_3464 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3464 j) = 166630380 := by decide
private theorem lowerTwo_row_3465 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3465 j) = 166355159 := by decide
private theorem lowerTwo_row_3466 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3466 j) = 166370725 := by decide
private theorem lowerTwo_row_3467 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3467 j) = 166095420 := by decide
private theorem lowerTwo_row_3468 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3468 j) = 166110995 := by decide
private theorem lowerTwo_row_3469 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3469 j) = 165835633 := by decide
private theorem lowerTwo_row_3470 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3470 j) = 165851211 := by decide
private theorem lowerTwo_row_3471 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3471 j) = 165575818 := by decide
private theorem lowerTwo_row_3472 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3472 j) = 165591411 := by decide
private theorem lowerTwo_row_3473 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3473 j) = 165315947 := by decide
private theorem lowerTwo_row_3474 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3474 j) = 165331540 := by decide
private theorem lowerTwo_row_3475 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3475 j) = 165056008 := by decide
private theorem lowerTwo_row_3476 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3476 j) = 165071622 := by decide
private theorem lowerTwo_row_3477 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3477 j) = 164796050 := by decide
private theorem lowerTwo_row_3478 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3478 j) = 164811678 := by decide
private theorem lowerTwo_row_3479 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3479 j) = 164536025 := by decide
private theorem lowerTwo_row_3480 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3480 j) = 164551663 := by decide
private theorem lowerTwo_row_3481 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3481 j) = 164275953 := by decide
private theorem lowerTwo_row_3482 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3482 j) = 164291601 := by decide
private theorem lowerTwo_row_3483 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3483 j) = 164015834 := by decide
private theorem lowerTwo_row_3484 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3484 j) = 164031504 := by decide
private theorem lowerTwo_row_3485 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3485 j) = 163755679 := by decide
private theorem lowerTwo_row_3486 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3486 j) = 163771347 := by decide
private theorem lowerTwo_row_3487 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3487 j) = 163495445 := by decide
private theorem lowerTwo_row_3488 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3488 j) = 163511140 := by decide
private theorem lowerTwo_row_3489 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3489 j) = 163235190 := by decide
private theorem lowerTwo_row_3490 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3490 j) = 163250895 := by decide
private theorem lowerTwo_row_3491 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3491 j) = 162974875 := by decide
private theorem lowerTwo_row_3492 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3492 j) = 162990595 := by decide
private theorem lowerTwo_row_3493 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3493 j) = 162714504 := by decide
private theorem lowerTwo_row_3494 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3494 j) = 162730233 := by decide
private theorem lowerTwo_row_3495 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3495 j) = 162454095 := by decide
private theorem lowerTwo_row_3496 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3496 j) = 162469815 := by decide
private theorem lowerTwo_row_3497 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3497 j) = 162193632 := by decide
private theorem lowerTwo_row_3498 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3498 j) = 162209361 := by decide
private theorem lowerTwo_row_3499 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3499 j) = 161933107 := by decide
private theorem lowerTwo_row_3500 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3500 j) = 161948850 := by decide
private theorem lowerTwo_row_3501 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3501 j) = 161672531 := by decide
private theorem lowerTwo_row_3502 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3502 j) = 161688270 := by decide
private theorem lowerTwo_row_3503 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3503 j) = 161411896 := by decide
private theorem lowerTwo_row_3504 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3504 j) = 161427661 := by decide
private theorem lowerTwo_row_3505 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3505 j) = 161151209 := by decide
private theorem lowerTwo_row_3506 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3506 j) = 161166998 := by decide
private theorem lowerTwo_row_3507 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3507 j) = 160890484 := by decide
private theorem lowerTwo_row_3508 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3508 j) = 160906265 := by decide
private theorem lowerTwo_row_3509 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3509 j) = 160629693 := by decide
private theorem lowerTwo_row_3510 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3510 j) = 160645484 := by decide
private theorem lowerTwo_row_3511 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3511 j) = 160368842 := by decide
private theorem lowerTwo_row_3512 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3512 j) = 160384661 := by decide
private theorem lowerTwo_row_3513 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3513 j) = 160107955 := by decide
private theorem lowerTwo_row_3514 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3514 j) = 160123777 := by decide
private theorem lowerTwo_row_3515 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3515 j) = 159847010 := by decide
private theorem lowerTwo_row_3516 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3516 j) = 159862836 := by decide
private theorem lowerTwo_row_3517 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3517 j) = 159586002 := by decide
private theorem lowerTwo_row_3518 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3518 j) = 159601840 := by decide
private theorem lowerTwo_row_3519 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3519 j) = 159324935 := by decide
private theorem lowerTwo_row_3520 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3520 j) = 159340789 := by decide
private theorem lowerTwo_row_3521 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3521 j) = 159063837 := by decide
private theorem lowerTwo_row_3522 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3522 j) = 159079681 := by decide
private theorem lowerTwo_row_3523 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3523 j) = 158802647 := by decide
private theorem lowerTwo_row_3524 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3524 j) = 158818517 := by decide
private theorem lowerTwo_row_3525 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3525 j) = 158541423 := by decide
private theorem lowerTwo_row_3526 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3526 j) = 158557277 := by decide
private theorem lowerTwo_row_3527 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3527 j) = 158280138 := by decide
private theorem lowerTwo_row_3528 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3528 j) = 158296015 := by decide
private theorem lowerTwo_row_3529 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3529 j) = 158018786 := by decide
private theorem lowerTwo_row_3530 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3530 j) = 158034672 := by decide
private theorem lowerTwo_row_3531 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3531 j) = 157757387 := by decide
private theorem lowerTwo_row_3532 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3532 j) = 157773280 := by decide
private theorem lowerTwo_row_3533 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3533 j) = 157495934 := by decide
private theorem lowerTwo_row_3534 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3534 j) = 157511836 := by decide
private theorem lowerTwo_row_3535 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3535 j) = 157234410 := by decide
private theorem lowerTwo_row_3536 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3536 j) = 157250326 := by decide
private theorem lowerTwo_row_3537 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3537 j) = 156972832 := by decide
private theorem lowerTwo_row_3538 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3538 j) = 156988758 := by decide
private theorem lowerTwo_row_3539 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3539 j) = 156711197 := by decide
private theorem lowerTwo_row_3540 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3540 j) = 156727134 := by decide
private theorem lowerTwo_row_3541 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3541 j) = 156449498 := by decide
private theorem lowerTwo_row_3542 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3542 j) = 156465440 := by decide
private theorem lowerTwo_row_3543 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3543 j) = 156187745 := by decide
private theorem lowerTwo_row_3544 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3544 j) = 156203688 := by decide
private theorem lowerTwo_row_3545 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3545 j) = 155925925 := by decide
private theorem lowerTwo_row_3546 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3546 j) = 155941886 := by decide
private theorem lowerTwo_row_3547 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3547 j) = 155664063 := by decide
private theorem lowerTwo_row_3548 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3548 j) = 155680020 := by decide
private theorem lowerTwo_row_3549 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3549 j) = 155402118 := by decide
private theorem lowerTwo_row_3550 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3550 j) = 155418082 := by decide
private theorem lowerTwo_row_3551 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3551 j) = 155140127 := by decide
private theorem lowerTwo_row_3552 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3552 j) = 155156107 := by decide
private theorem lowerTwo_row_3553 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3553 j) = 154878063 := by decide
private theorem lowerTwo_row_3554 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3554 j) = 154894048 := by decide
private theorem lowerTwo_row_3555 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3555 j) = 154615940 := by decide
private theorem lowerTwo_row_3556 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3556 j) = 154631925 := by decide
private theorem lowerTwo_row_3557 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3557 j) = 154353775 := by decide
private theorem lowerTwo_row_3558 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3558 j) = 154369744 := by decide
private theorem lowerTwo_row_3559 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3559 j) = 154091512 := by decide
private theorem lowerTwo_row_3560 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3560 j) = 154107516 := by decide
private theorem lowerTwo_row_3561 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3561 j) = 153829208 := by decide
private theorem lowerTwo_row_3562 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3562 j) = 153845226 := by decide
private theorem lowerTwo_row_3563 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3563 j) = 153566840 := by decide
private theorem lowerTwo_row_3564 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3564 j) = 153582840 := by decide
private theorem lowerTwo_row_3565 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3565 j) = 153304398 := by decide
private theorem lowerTwo_row_3566 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3566 j) = 153320414 := by decide
private theorem lowerTwo_row_3567 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3567 j) = 153041887 := by decide
private theorem lowerTwo_row_3568 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3568 j) = 153057918 := by decide
private theorem lowerTwo_row_3569 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3569 j) = 152779324 := by decide
private theorem lowerTwo_row_3570 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3570 j) = 152795366 := by decide
private theorem lowerTwo_row_3571 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3571 j) = 152516706 := by decide
private theorem lowerTwo_row_3572 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3572 j) = 152532741 := by decide
private theorem lowerTwo_row_3573 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3573 j) = 152254001 := by decide
private theorem lowerTwo_row_3574 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3574 j) = 152270062 := by decide
private theorem lowerTwo_row_3575 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3575 j) = 151991245 := by decide
private theorem lowerTwo_row_3576 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3576 j) = 152007296 := by decide
private theorem lowerTwo_row_3577 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3577 j) = 151728426 := by decide
private theorem lowerTwo_row_3578 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3578 j) = 151744486 := by decide
private theorem lowerTwo_row_3579 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3579 j) = 151465528 := by decide
private theorem lowerTwo_row_3580 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3580 j) = 151481589 := by decide
private theorem lowerTwo_row_3581 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3581 j) = 151202577 := by decide
private theorem lowerTwo_row_3582 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3582 j) = 151218640 := by decide
private theorem lowerTwo_row_3583 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3583 j) = 150939545 := by decide
private theorem lowerTwo_row_3584 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3584 j) = 150955622 := by decide
private theorem lowerTwo_row_3585 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3585 j) = 150676441 := by decide
private theorem lowerTwo_row_3586 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3586 j) = 150692520 := by decide
private theorem lowerTwo_row_3587 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3587 j) = 150413295 := by decide
private theorem lowerTwo_row_3588 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3588 j) = 150429376 := by decide
private theorem lowerTwo_row_3589 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3589 j) = 150150048 := by decide
private theorem lowerTwo_row_3590 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3590 j) = 150166145 := by decide
private theorem lowerTwo_row_3591 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3591 j) = 149886754 := by decide
private theorem lowerTwo_row_3592 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3592 j) = 149902852 := by decide
private theorem lowerTwo_row_3593 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3593 j) = 149623400 := by decide
private theorem lowerTwo_row_3594 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3594 j) = 149639492 := by decide
private theorem lowerTwo_row_3595 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3595 j) = 149359949 := by decide
private theorem lowerTwo_row_3596 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3596 j) = 149376059 := by decide
private theorem lowerTwo_row_3597 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3597 j) = 149096451 := by decide
private theorem lowerTwo_row_3598 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3598 j) = 149112557 := by decide
private theorem lowerTwo_row_3599 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3599 j) = 148832867 := by decide
private theorem lowerTwo_row_3600 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3600 j) = 148848980 := by decide
private theorem lowerTwo_row_3601 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3601 j) = 148569222 := by decide
private theorem lowerTwo_row_3602 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3602 j) = 148585340 := by decide
private theorem lowerTwo_row_3603 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3603 j) = 148305513 := by decide
private theorem lowerTwo_row_3604 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3604 j) = 148321625 := by decide
private theorem lowerTwo_row_3605 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3605 j) = 148041720 := by decide
private theorem lowerTwo_row_3606 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3606 j) = 148057851 := by decide
private theorem lowerTwo_row_3607 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3607 j) = 147777866 := by decide
private theorem lowerTwo_row_3608 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3608 j) = 147793979 := by decide
private theorem lowerTwo_row_3609 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3609 j) = 147513934 := by decide
private theorem lowerTwo_row_3610 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3610 j) = 147530071 := by decide
private theorem lowerTwo_row_3611 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3611 j) = 147249929 := by decide
private theorem lowerTwo_row_3612 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3612 j) = 147266060 := by decide
private theorem lowerTwo_row_3613 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3613 j) = 146985860 := by decide
private theorem lowerTwo_row_3614 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3614 j) = 147001990 := by decide
private theorem lowerTwo_row_3615 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3615 j) = 146721695 := by decide
private theorem lowerTwo_row_3616 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3616 j) = 146737863 := by decide
private theorem lowerTwo_row_3617 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3617 j) = 146457474 := by decide
private theorem lowerTwo_row_3618 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3618 j) = 146473634 := by decide
private theorem lowerTwo_row_3619 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3619 j) = 146193180 := by decide
private theorem lowerTwo_row_3620 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3620 j) = 146209332 := by decide
private theorem lowerTwo_row_3621 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3621 j) = 145928818 := by decide
private theorem lowerTwo_row_3622 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3622 j) = 145944974 := by decide
private theorem lowerTwo_row_3623 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3623 j) = 145664357 := by decide
private theorem lowerTwo_row_3624 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3624 j) = 145680522 := by decide
private theorem lowerTwo_row_3625 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3625 j) = 145399856 := by decide
private theorem lowerTwo_row_3626 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3626 j) = 145416008 := by decide
private theorem lowerTwo_row_3627 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3627 j) = 145135253 := by decide
private theorem lowerTwo_row_3628 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3628 j) = 145151419 := by decide
private theorem lowerTwo_row_3629 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3629 j) = 144870576 := by decide
private theorem lowerTwo_row_3630 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3630 j) = 144886761 := by decide
private theorem lowerTwo_row_3631 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3631 j) = 144605837 := by decide
private theorem lowerTwo_row_3632 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3632 j) = 144622003 := by decide
private theorem lowerTwo_row_3633 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3633 j) = 144341011 := by decide
private theorem lowerTwo_row_3634 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3634 j) = 144357191 := by decide
private theorem lowerTwo_row_3635 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3635 j) = 144076127 := by decide
private theorem lowerTwo_row_3636 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3636 j) = 144092297 := by decide
private theorem lowerTwo_row_3637 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3637 j) = 143811135 := by decide
private theorem lowerTwo_row_3638 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3638 j) = 143827318 := by decide
private theorem lowerTwo_row_3639 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3639 j) = 143546095 := by decide
private theorem lowerTwo_row_3640 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3640 j) = 143562275 := by decide
private theorem lowerTwo_row_3641 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3641 j) = 143280968 := by decide
private theorem lowerTwo_row_3642 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3642 j) = 143297139 := by decide
private theorem lowerTwo_row_3643 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3643 j) = 143015747 := by decide
private theorem lowerTwo_row_3644 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3644 j) = 143031932 := by decide
private theorem lowerTwo_row_3645 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3645 j) = 142750465 := by decide
private theorem lowerTwo_row_3646 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3646 j) = 142766653 := by decide
private theorem lowerTwo_row_3647 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3647 j) = 142485087 := by decide
private theorem lowerTwo_row_3648 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3648 j) = 142501294 := by decide
private theorem lowerTwo_row_3649 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3649 j) = 142219645 := by decide
private theorem lowerTwo_row_3650 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3650 j) = 142235842 := by decide
private theorem lowerTwo_row_3651 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3651 j) = 141954119 := by decide
private theorem lowerTwo_row_3652 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3652 j) = 141970317 := by decide
private theorem lowerTwo_row_3653 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3653 j) = 141688518 := by decide
private theorem lowerTwo_row_3654 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3654 j) = 141704716 := by decide
private theorem lowerTwo_row_3655 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3655 j) = 141422841 := by decide
private theorem lowerTwo_row_3656 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3656 j) = 141439022 := by decide
private theorem lowerTwo_row_3657 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3657 j) = 141157071 := by decide
private theorem lowerTwo_row_3658 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3658 j) = 141173253 := by decide
private theorem lowerTwo_row_3659 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3659 j) = 140891221 := by decide
private theorem lowerTwo_row_3660 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3660 j) = 140907431 := by decide
private theorem lowerTwo_row_3661 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3661 j) = 140625292 := by decide
private theorem lowerTwo_row_3662 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3662 j) = 140641494 := by decide
private theorem lowerTwo_row_3663 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3663 j) = 140359282 := by decide
private theorem lowerTwo_row_3664 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3664 j) = 140375480 := by decide
private theorem lowerTwo_row_3665 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3665 j) = 140093201 := by decide
private theorem lowerTwo_row_3666 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3666 j) = 140109379 := by decide
private theorem lowerTwo_row_3667 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3667 j) = 139827022 := by decide
private theorem lowerTwo_row_3668 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3668 j) = 139843217 := by decide
private theorem lowerTwo_row_3669 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3669 j) = 139560761 := by decide
private theorem lowerTwo_row_3670 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3670 j) = 139576961 := by decide
private theorem lowerTwo_row_3671 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3671 j) = 139294425 := by decide
private theorem lowerTwo_row_3672 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3672 j) = 139310614 := by decide
private theorem lowerTwo_row_3673 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3673 j) = 139027984 := by decide
private theorem lowerTwo_row_3674 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3674 j) = 139044191 := by decide
private theorem lowerTwo_row_3675 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3675 j) = 138761482 := by decide
private theorem lowerTwo_row_3676 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3676 j) = 138777662 := by decide
private theorem lowerTwo_row_3677 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3677 j) = 138494895 := by decide
private theorem lowerTwo_row_3678 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3678 j) = 138511076 := by decide
private theorem lowerTwo_row_3679 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3679 j) = 138228218 := by decide
private theorem lowerTwo_row_3680 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3680 j) = 138244407 := by decide
private theorem lowerTwo_row_3681 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3681 j) = 137961435 := by decide
private theorem lowerTwo_row_3682 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3682 j) = 137977645 := by decide
private theorem lowerTwo_row_3683 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3683 j) = 137694601 := by decide
private theorem lowerTwo_row_3684 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3684 j) = 137710797 := by decide
private theorem lowerTwo_row_3685 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3685 j) = 137427661 := by decide
private theorem lowerTwo_row_3686 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3686 j) = 137443852 := by decide
private theorem lowerTwo_row_3687 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3687 j) = 137160627 := by decide
private theorem lowerTwo_row_3688 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3688 j) = 137176826 := by decide
private theorem lowerTwo_row_3689 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3689 j) = 136893519 := by decide
private theorem lowerTwo_row_3690 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3690 j) = 136909715 := by decide
private theorem lowerTwo_row_3691 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3691 j) = 136626319 := by decide
private theorem lowerTwo_row_3692 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3692 j) = 136642521 := by decide
private theorem lowerTwo_row_3693 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3693 j) = 136359035 := by decide
private theorem lowerTwo_row_3694 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3694 j) = 136375237 := by decide
private theorem lowerTwo_row_3695 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3695 j) = 136091670 := by decide
private theorem lowerTwo_row_3696 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3696 j) = 136107866 := by decide
private theorem lowerTwo_row_3697 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3697 j) = 135824202 := by decide
private theorem lowerTwo_row_3698 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3698 j) = 135840401 := by decide
private theorem lowerTwo_row_3699 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3699 j) = 135556656 := by decide
private theorem lowerTwo_row_3700 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3700 j) = 135572851 := by decide
private theorem lowerTwo_row_3701 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3701 j) = 135289024 := by decide
private theorem lowerTwo_row_3702 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3702 j) = 135305213 := by decide
private theorem lowerTwo_row_3703 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3703 j) = 135021285 := by decide
private theorem lowerTwo_row_3704 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3704 j) = 135037477 := by decide
private theorem lowerTwo_row_3705 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3705 j) = 134753468 := by decide
private theorem lowerTwo_row_3706 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3706 j) = 134769656 := by decide
private theorem lowerTwo_row_3707 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3707 j) = 134485565 := by decide
private theorem lowerTwo_row_3708 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3708 j) = 134501752 := by decide
private theorem lowerTwo_row_3709 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3709 j) = 134217568 := by decide
private theorem lowerTwo_row_3710 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3710 j) = 134233754 := by decide
private theorem lowerTwo_row_3711 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3711 j) = 133949468 := by decide
private theorem lowerTwo_row_3712 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3712 j) = 133965653 := by decide
private theorem lowerTwo_row_3713 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3713 j) = 133681299 := by decide
private theorem lowerTwo_row_3714 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3714 j) = 133697467 := by decide
private theorem lowerTwo_row_3715 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3715 j) = 133413021 := by decide
private theorem lowerTwo_row_3716 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3716 j) = 133429194 := by decide
private theorem lowerTwo_row_3717 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3717 j) = 133144652 := by decide
private theorem lowerTwo_row_3718 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3718 j) = 133160835 := by decide
private theorem lowerTwo_row_3719 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3719 j) = 132876200 := by decide
private theorem lowerTwo_row_3720 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3720 j) = 132892372 := by decide
private theorem lowerTwo_row_3721 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3721 j) = 132607651 := by decide
private theorem lowerTwo_row_3722 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3722 j) = 132623814 := by decide
private theorem lowerTwo_row_3723 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3723 j) = 132338994 := by decide
private theorem lowerTwo_row_3724 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3724 j) = 132355160 := by decide
private theorem lowerTwo_row_3725 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3725 j) = 132070272 := by decide
private theorem lowerTwo_row_3726 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3726 j) = 132086428 := by decide
private theorem lowerTwo_row_3727 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3727 j) = 131801425 := by decide
private theorem lowerTwo_row_3728 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3728 j) = 131817589 := by decide
private theorem lowerTwo_row_3729 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3729 j) = 131532495 := by decide
private theorem lowerTwo_row_3730 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3730 j) = 131548659 := by decide
private theorem lowerTwo_row_3731 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3731 j) = 131263476 := by decide
private theorem lowerTwo_row_3732 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3732 j) = 131279625 := by decide
private theorem lowerTwo_row_3733 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3733 j) = 130994356 := by decide
private theorem lowerTwo_row_3734 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3734 j) = 131010519 := by decide
private theorem lowerTwo_row_3735 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3735 j) = 130725154 := by decide
private theorem lowerTwo_row_3736 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3736 j) = 130741299 := by decide
private theorem lowerTwo_row_3737 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3737 j) = 130455837 := by decide
private theorem lowerTwo_row_3738 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3738 j) = 130471980 := by decide
private theorem lowerTwo_row_3739 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3739 j) = 130186433 := by decide
private theorem lowerTwo_row_3740 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3740 j) = 130202575 := by decide
private theorem lowerTwo_row_3741 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3741 j) = 129916932 := by decide
private theorem lowerTwo_row_3742 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3742 j) = 129933065 := by decide
private theorem lowerTwo_row_3743 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3743 j) = 129647333 := by decide
private theorem lowerTwo_row_3744 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3744 j) = 129663455 := by decide
private theorem lowerTwo_row_3745 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3745 j) = 129377633 := by decide
private theorem lowerTwo_row_3746 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3746 j) = 129393761 := by decide
private theorem lowerTwo_row_3747 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3747 j) = 129107840 := by decide
private theorem lowerTwo_row_3748 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3748 j) = 129123968 := by decide
private theorem lowerTwo_row_3749 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3749 j) = 128837937 := by decide
private theorem lowerTwo_row_3750 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3750 j) = 128854058 := by decide
private theorem lowerTwo_row_3751 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3751 j) = 128567943 := by decide
private theorem lowerTwo_row_3752 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3752 j) = 128584054 := by decide
private theorem lowerTwo_row_3753 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3753 j) = 128297859 := by decide
private theorem lowerTwo_row_3754 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3754 j) = 128313966 := by decide
private theorem lowerTwo_row_3755 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3755 j) = 128027660 := by decide
private theorem lowerTwo_row_3756 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3756 j) = 128043769 := by decide
private theorem lowerTwo_row_3757 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3757 j) = 127757368 := by decide
private theorem lowerTwo_row_3758 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3758 j) = 127773473 := by decide
private theorem lowerTwo_row_3759 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3759 j) = 127486974 := by decide
private theorem lowerTwo_row_3760 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3760 j) = 127503077 := by decide
private theorem lowerTwo_row_3761 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3761 j) = 127216475 := by decide
private theorem lowerTwo_row_3762 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3762 j) = 127232569 := by decide
private theorem lowerTwo_row_3763 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3763 j) = 126945882 := by decide
private theorem lowerTwo_row_3764 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3764 j) = 126961971 := by decide
private theorem lowerTwo_row_3765 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3765 j) = 126675182 := by decide
private theorem lowerTwo_row_3766 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3766 j) = 126691264 := by decide
private theorem lowerTwo_row_3767 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3767 j) = 126404388 := by decide
private theorem lowerTwo_row_3768 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3768 j) = 126420468 := by decide
private theorem lowerTwo_row_3769 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3769 j) = 126133477 := by decide
private theorem lowerTwo_row_3770 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3770 j) = 126149554 := by decide
private theorem lowerTwo_row_3771 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3771 j) = 125862487 := by decide
private theorem lowerTwo_row_3772 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3772 j) = 125878556 := by decide
private theorem lowerTwo_row_3773 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3773 j) = 125591383 := by decide
private theorem lowerTwo_row_3774 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3774 j) = 125607429 := by decide
private theorem lowerTwo_row_3775 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3775 j) = 125320163 := by decide
private theorem lowerTwo_row_3776 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3776 j) = 125336205 := by decide
private theorem lowerTwo_row_3777 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3777 j) = 125048844 := by decide
private theorem lowerTwo_row_3778 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3778 j) = 125064902 := by decide
private theorem lowerTwo_row_3779 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3779 j) = 124777434 := by decide
private theorem lowerTwo_row_3780 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3780 j) = 124793474 := by decide
private theorem lowerTwo_row_3781 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3781 j) = 124505897 := by decide
private theorem lowerTwo_row_3782 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3782 j) = 124521943 := by decide
private theorem lowerTwo_row_3783 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3783 j) = 124234268 := by decide
private theorem lowerTwo_row_3784 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3784 j) = 124250297 := by decide
private theorem lowerTwo_row_3785 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3785 j) = 123962544 := by decide
private theorem lowerTwo_row_3786 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3786 j) = 123978548 := by decide
private theorem lowerTwo_row_3787 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3787 j) = 123690698 := by decide
private theorem lowerTwo_row_3788 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3788 j) = 123706703 := by decide
private theorem lowerTwo_row_3789 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3789 j) = 123418747 := by decide
private theorem lowerTwo_row_3790 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3790 j) = 123434764 := by decide
private theorem lowerTwo_row_3791 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3791 j) = 123146695 := by decide
private theorem lowerTwo_row_3792 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3792 j) = 123162697 := by decide
private theorem lowerTwo_row_3793 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3793 j) = 122874538 := by decide
private theorem lowerTwo_row_3794 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3794 j) = 122890521 := by decide
private theorem lowerTwo_row_3795 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3795 j) = 122602256 := by decide
private theorem lowerTwo_row_3796 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3796 j) = 122618250 := by decide
private theorem lowerTwo_row_3797 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3797 j) = 122329871 := by decide
private theorem lowerTwo_row_3798 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3798 j) = 122345857 := by decide
private theorem lowerTwo_row_3799 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3799 j) = 122057386 := by decide
private theorem lowerTwo_row_3800 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3800 j) = 122073359 := by decide
private theorem lowerTwo_row_3801 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3801 j) = 121784801 := by decide
private theorem lowerTwo_row_3802 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3802 j) = 121800760 := by decide
private theorem lowerTwo_row_3803 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3803 j) = 121512093 := by decide
private theorem lowerTwo_row_3804 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3804 j) = 121528052 := by decide
private theorem lowerTwo_row_3805 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3805 j) = 121239284 := by decide
private theorem lowerTwo_row_3806 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3806 j) = 121255227 := by decide
private theorem lowerTwo_row_3807 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3807 j) = 120966351 := by decide
private theorem lowerTwo_row_3808 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3808 j) = 120982303 := by decide
private theorem lowerTwo_row_3809 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3809 j) = 120693314 := by decide
private theorem lowerTwo_row_3810 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3810 j) = 120709258 := by decide
private theorem lowerTwo_row_3811 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3811 j) = 120420176 := by decide
private theorem lowerTwo_row_3812 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3812 j) = 120436099 := by decide
private theorem lowerTwo_row_3813 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3813 j) = 120146927 := by decide
private theorem lowerTwo_row_3814 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3814 j) = 120162835 := by decide
private theorem lowerTwo_row_3815 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3815 j) = 119873558 := by decide
private theorem lowerTwo_row_3816 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3816 j) = 120200718 := by decide
private theorem lowerTwo_row_3817 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3817 j) = 121156859 := by decide
private theorem lowerTwo_row_3818 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3818 j) = 122419060 := by decide
private theorem lowerTwo_row_3819 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3819 j) = 123376654 := by decide
private theorem lowerTwo_row_3820 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3820 j) = 124640398 := by decide
private theorem lowerTwo_row_3821 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3821 j) = 125599444 := by decide
private theorem lowerTwo_row_3822 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3822 j) = 126864738 := by decide
private theorem lowerTwo_row_3823 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3823 j) = 127825270 := by decide
private theorem lowerTwo_row_3824 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3824 j) = 129092155 := by decide
private theorem lowerTwo_row_3825 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3825 j) = 130054172 := by decide
private theorem lowerTwo_row_3826 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3826 j) = 131322663 := by decide
private theorem lowerTwo_row_3827 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3827 j) = 132286186 := by decide
private theorem lowerTwo_row_3828 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3828 j) = 133556286 := by decide
private theorem lowerTwo_row_3829 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3829 j) = 134521357 := by decide
private theorem lowerTwo_row_3830 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3830 j) = 135793100 := by decide
private theorem lowerTwo_row_3831 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3831 j) = 136759703 := by decide
private theorem lowerTwo_row_3832 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3832 j) = 138033103 := by decide
private theorem lowerTwo_row_3833 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3833 j) = 139001291 := by decide
private theorem lowerTwo_row_3834 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3834 j) = 140276360 := by decide
private theorem lowerTwo_row_3835 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3835 j) = 141246128 := by decide
private theorem lowerTwo_row_3836 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3836 j) = 142522909 := by decide
private theorem lowerTwo_row_3837 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3837 j) = 143494292 := by decide
private theorem lowerTwo_row_3838 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3838 j) = 144772770 := by decide
private theorem lowerTwo_row_3839 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3839 j) = 145745788 := by decide
private theorem lowerTwo_row_3840 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3840 j) = 147026014 := by decide
private theorem lowerTwo_row_3841 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3841 j) = 148000672 := by decide
private theorem lowerTwo_row_3842 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3842 j) = 149282632 := by decide
private theorem lowerTwo_row_3843 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3843 j) = 150258971 := by decide
private theorem lowerTwo_row_3844 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3844 j) = 151542715 := by decide
private theorem lowerTwo_row_3845 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3845 j) = 152520733 := by decide
private theorem lowerTwo_row_3846 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3846 j) = 153806276 := by decide
private theorem lowerTwo_row_3847 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3847 j) = 154785994 := by decide
private theorem lowerTwo_row_3848 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3848 j) = 156073364 := by decide
private theorem lowerTwo_row_3849 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3849 j) = 157054818 := by decide
private theorem lowerTwo_row_3850 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3850 j) = 158344021 := by decide
private theorem lowerTwo_row_3851 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3851 j) = 159327210 := by decide
private theorem lowerTwo_row_3852 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3852 j) = 160618265 := by decide
private theorem lowerTwo_row_3853 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3853 j) = 161603218 := by decide
private theorem lowerTwo_row_3854 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3854 j) = 162896162 := by decide
private theorem lowerTwo_row_3855 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3855 j) = 163882913 := by decide
private theorem lowerTwo_row_3856 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3856 j) = 165177777 := by decide
private theorem lowerTwo_row_3857 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3857 j) = 166166309 := by decide
private theorem lowerTwo_row_3858 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3858 j) = 167463068 := by decide
private theorem lowerTwo_row_3859 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3859 j) = 168453480 := by decide
private theorem lowerTwo_row_3860 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3860 j) = 169752162 := by decide
private theorem lowerTwo_row_3861 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3861 j) = 170744426 := by decide
private theorem lowerTwo_row_3862 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3862 j) = 172045071 := by decide
private theorem lowerTwo_row_3863 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3863 j) = 173039203 := by decide
private theorem lowerTwo_row_3864 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3864 j) = 174341837 := by decide
private theorem lowerTwo_row_3865 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3865 j) = 175337877 := by decide
private theorem lowerTwo_row_3866 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3866 j) = 176642516 := by decide
private theorem lowerTwo_row_3867 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3867 j) = 177640473 := by decide
private theorem lowerTwo_row_3868 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3868 j) = 178947137 := by decide
private theorem lowerTwo_row_3869 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3869 j) = 179947027 := by decide
private theorem lowerTwo_row_3870 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3870 j) = 181255747 := by decide
private theorem lowerTwo_row_3871 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3871 j) = 182257618 := by decide
private theorem lowerTwo_row_3872 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3872 j) = 183568398 := by decide
private theorem lowerTwo_row_3873 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3873 j) = 184572257 := by decide
private theorem lowerTwo_row_3874 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3874 j) = 185885135 := by decide
private theorem lowerTwo_row_3875 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3875 j) = 186890976 := by decide
private theorem lowerTwo_row_3876 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3876 j) = 188206003 := by decide
private theorem lowerTwo_row_3877 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3877 j) = 189213864 := by decide
private theorem lowerTwo_row_3878 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3878 j) = 190531032 := by decide
private theorem lowerTwo_row_3879 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3879 j) = 191540944 := by decide
private theorem lowerTwo_row_3880 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3880 j) = 192860263 := by decide
private theorem lowerTwo_row_3881 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3881 j) = 193872303 := by decide
private theorem lowerTwo_row_3882 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3882 j) = 195193797 := by decide
private theorem lowerTwo_row_3883 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3883 j) = 196207895 := by decide
private theorem lowerTwo_row_3884 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3884 j) = 197531621 := by decide
private theorem lowerTwo_row_3885 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3885 j) = 198547866 := by decide
private theorem lowerTwo_row_3886 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3886 j) = 199873820 := by decide
private theorem lowerTwo_row_3887 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3887 j) = 200892193 := by decide
private theorem lowerTwo_row_3888 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3888 j) = 202220416 := by decide
private theorem lowerTwo_row_3889 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3889 j) = 203240963 := by decide
private theorem lowerTwo_row_3890 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3890 j) = 204571467 := by decide
private theorem lowerTwo_row_3891 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3891 j) = 205594233 := by decide
private theorem lowerTwo_row_3892 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3892 j) = 206927034 := by decide
private theorem lowerTwo_row_3893 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3893 j) = 207951997 := by decide
private theorem lowerTwo_row_3894 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3894 j) = 209287156 := by decide
private theorem lowerTwo_row_3895 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3895 j) = 210314379 := by decide
private theorem lowerTwo_row_3896 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3896 j) = 211651879 := by decide
private theorem lowerTwo_row_3897 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3897 j) = 212681370 := by decide
private theorem lowerTwo_row_3898 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3898 j) = 214021253 := by decide
private theorem lowerTwo_row_3899 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3899 j) = 215053054 := by decide
private theorem lowerTwo_row_3900 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3900 j) = 216395340 := by decide
private theorem lowerTwo_row_3901 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3901 j) = 217429453 := by decide
private theorem lowerTwo_row_3902 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3902 j) = 218774180 := by decide
private theorem lowerTwo_row_3903 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3903 j) = 219810656 := by decide
private theorem lowerTwo_row_3904 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3904 j) = 221157824 := by decide
private theorem lowerTwo_row_3905 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3905 j) = 222196665 := by decide
private theorem lowerTwo_row_3906 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3906 j) = 223546350 := by decide
private theorem lowerTwo_row_3907 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3907 j) = 224587592 := by decide
private theorem lowerTwo_row_3908 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3908 j) = 225939786 := by decide
private theorem lowerTwo_row_3909 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3909 j) = 226983428 := by decide
private theorem lowerTwo_row_3910 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3910 j) = 228338188 := by decide
private theorem lowerTwo_row_3911 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3911 j) = 229384299 := by decide
private theorem lowerTwo_row_3912 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3912 j) = 230741600 := by decide
private theorem lowerTwo_row_3913 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3913 j) = 231790171 := by decide
private theorem lowerTwo_row_3914 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3914 j) = 233150085 := by decide
private theorem lowerTwo_row_3915 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3915 j) = 234201201 := by decide
private theorem lowerTwo_row_3916 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3916 j) = 235563703 := by decide
private theorem lowerTwo_row_3917 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3917 j) = 236617343 := by decide
private theorem lowerTwo_row_3918 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3918 j) = 237982500 := by decide
private theorem lowerTwo_row_3919 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3919 j) = 239038723 := by decide
private theorem lowerTwo_row_3920 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3920 j) = 240406570 := by decide
private theorem lowerTwo_row_3921 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3921 j) = 241465362 := by decide
private theorem lowerTwo_row_3922 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3922 j) = 242835909 := by decide
private theorem lowerTwo_row_3923 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3923 j) = 243897310 := by decide
private theorem lowerTwo_row_3924 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3924 j) = 245270624 := by decide
private theorem lowerTwo_row_3925 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3925 j) = 246334670 := by decide
private theorem lowerTwo_row_3926 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3926 j) = 247710742 := by decide
private theorem lowerTwo_row_3927 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3927 j) = 248777465 := by decide
private theorem lowerTwo_row_3928 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3928 j) = 250158554 := by decide
private theorem lowerTwo_row_3929 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3929 j) = 251233625 := by decide
private theorem lowerTwo_row_3930 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3930 j) = 252624387 := by decide
private theorem lowerTwo_row_3931 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3931 j) = 253709197 := by decide
private theorem lowerTwo_row_3932 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3932 j) = 255109846 := by decide
private theorem lowerTwo_row_3933 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3933 j) = 256204458 := by decide
private theorem lowerTwo_row_3934 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3934 j) = 257615112 := by decide
private theorem lowerTwo_row_3935 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3935 j) = 258719648 := by decide
private theorem lowerTwo_row_3936 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3936 j) = 260140415 := by decide
private theorem lowerTwo_row_3937 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3937 j) = 261255042 := by decide
private theorem lowerTwo_row_3938 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3938 j) = 262686003 := by decide
private theorem lowerTwo_row_3939 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3939 j) = 263810801 := by decide
private theorem lowerTwo_row_3940 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3940 j) = 265252173 := by decide
private theorem lowerTwo_row_3941 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3941 j) = 266387240 := by decide
private theorem lowerTwo_row_3942 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3942 j) = 267839091 := by decide
private theorem lowerTwo_row_3943 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3943 j) = 268984625 := by decide
private theorem lowerTwo_row_3944 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3944 j) = 270447057 := by decide
private theorem lowerTwo_row_3945 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3945 j) = 271603171 := by decide
private theorem lowerTwo_row_3946 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3946 j) = 273076318 := by decide
private theorem lowerTwo_row_3947 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3947 j) = 274243130 := by decide
private theorem lowerTwo_row_3948 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3948 j) = 275727178 := by decide
private theorem lowerTwo_row_3949 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3949 j) = 276904782 := by decide
private theorem lowerTwo_row_3950 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3950 j) = 278399855 := by decide
private theorem lowerTwo_row_3951 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3951 j) = 279588427 := by decide
private theorem lowerTwo_row_3952 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3952 j) = 281094597 := by decide
private theorem lowerTwo_row_3953 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3953 j) = 282294318 := by decide
private theorem lowerTwo_row_3954 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3954 j) = 283811767 := by decide
private theorem lowerTwo_row_3955 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3955 j) = 285022704 := by decide
private theorem lowerTwo_row_3956 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3956 j) = 286551593 := by decide
private theorem lowerTwo_row_3957 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3957 j) = 287773912 := by decide
private theorem lowerTwo_row_3958 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3958 j) = 289314349 := by decide
private theorem lowerTwo_row_3959 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3959 j) = 290548246 := by decide
private theorem lowerTwo_row_3960 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3960 j) = 292100350 := by decide
private theorem lowerTwo_row_3961 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3961 j) = 293345920 := by decide
private theorem lowerTwo_row_3962 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3962 j) = 294909925 := by decide
private theorem lowerTwo_row_3963 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3963 j) = 296167284 := by decide
private theorem lowerTwo_row_3964 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3964 j) = 297743309 := by decide
private theorem lowerTwo_row_3965 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3965 j) = 299012643 := by decide
private theorem lowerTwo_row_3966 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3966 j) = 300600802 := by decide
private theorem lowerTwo_row_3967 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3967 j) = 301882321 := by decide
private theorem lowerTwo_row_3968 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3968 j) = 303482782 := by decide
private theorem lowerTwo_row_3969 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3969 j) = 304776565 := by decide
private theorem lowerTwo_row_3970 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3970 j) = 306389543 := by decide
private theorem lowerTwo_row_3971 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3971 j) = 307648891 := by decide
private theorem lowerTwo_row_3972 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3972 j) = 309089042 := by decide
private theorem lowerTwo_row_3973 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3973 j) = 310272486 := by decide
private theorem lowerTwo_row_3974 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3974 j) = 311731656 := by decide
private theorem lowerTwo_row_3975 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3975 j) = 312887170 := by decide
private theorem lowerTwo_row_3976 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3976 j) = 314412647 := by decide
private theorem lowerTwo_row_3977 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3977 j) = 315587491 := by decide
private theorem lowerTwo_row_3978 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3978 j) = 317085493 := by decide
private theorem lowerTwo_row_3979 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3979 j) = 318326800 := by decide
private theorem lowerTwo_row_3980 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3980 j) = 319843855 := by decide
private theorem lowerTwo_row_3981 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3981 j) = 321056574 := by decide
private theorem lowerTwo_row_3982 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3982 j) = 322639267 := by decide
private theorem lowerTwo_row_3983 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3983 j) = 323870659 := by decide
private theorem lowerTwo_row_3984 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3984 j) = 325425181 := by decide
private theorem lowerTwo_row_3985 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3985 j) = 326722480 := by decide
private theorem lowerTwo_row_3986 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3986 j) = 328296179 := by decide
private theorem lowerTwo_row_3987 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3987 j) = 329565579 := by decide
private theorem lowerTwo_row_3988 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3988 j) = 331205699 := by decide
private theorem lowerTwo_row_3989 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3989 j) = 332494577 := by decide
private theorem lowerTwo_row_3990 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3990 j) = 334107271 := by decide
private theorem lowerTwo_row_3991 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3991 j) = 335462929 := by decide
private theorem lowerTwo_row_3992 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3992 j) = 337095608 := by decide
private theorem lowerTwo_row_3993 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3993 j) = 338424055 := by decide
private theorem lowerTwo_row_3994 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3994 j) = 340124099 := by decide
private theorem lowerTwo_row_3995 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3995 j) = 341472646 := by decide
private theorem lowerTwo_row_3996 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3996 j) = 343145152 := by decide
private theorem lowerTwo_row_3997 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3997 j) = 344560102 := by decide
private theorem lowerTwo_row_3998 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3998 j) = 346252063 := by decide
private theorem lowerTwo_row_3999 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3999 j) = 347639256 := by decide
private theorem lowerTwo_row_4000 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4000 j) = 349398160 := by decide
private theorem lowerTwo_row_4001 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4001 j) = 350805161 := by decide
private theorem lowerTwo_row_4002 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4002 j) = 352536816 := by decide
private theorem lowerTwo_row_4003 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4003 j) = 354011045 := by decide
private theorem lowerTwo_row_4004 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4004 j) = 355763012 := by decide
private theorem lowerTwo_row_4005 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4005 j) = 357210356 := by decide
private theorem lowerTwo_row_4006 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4006 j) = 359030155 := by decide
private theorem lowerTwo_row_4007 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4007 j) = 360498059 := by decide
private theorem lowerTwo_row_4008 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4008 j) = 362291508 := by decide
private theorem lowerTwo_row_4009 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4009 j) = 363827646 := by decide
private theorem lowerTwo_row_4010 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4010 j) = 365641875 := by decide
private theorem lowerTwo_row_4011 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4011 j) = 367151040 := by decide
private theorem lowerTwo_row_4012 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4012 j) = 369032807 := by decide
private theorem lowerTwo_row_4013 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4013 j) = 370562237 := by decide
private theorem lowerTwo_row_4014 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4014 j) = 372417275 := by decide
private theorem lowerTwo_row_4015 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4015 j) = 374014557 := by decide
private theorem lowerTwo_row_4016 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4016 j) = 375890454 := by decide
private theorem lowerTwo_row_4017 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4017 j) = 377461314 := by decide
private theorem lowerTwo_row_4018 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4018 j) = 379405667 := by decide
private theorem lowerTwo_row_4019 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4019 j) = 380997775 := by decide
private theorem lowerTwo_row_4020 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4020 j) = 382916218 := by decide
private theorem lowerTwo_row_4021 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4021 j) = 384577121 := by decide
private theorem lowerTwo_row_4022 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4022 j) = 386517420 := by decide
private theorem lowerTwo_row_4023 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4023 j) = 388152761 := by decide
private theorem lowerTwo_row_4024 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4024 j) = 390162080 := by decide
private theorem lowerTwo_row_4025 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4025 j) = 391818640 := by decide
private theorem lowerTwo_row_4026 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4026 j) = 393801797 := by decide
private theorem lowerTwo_row_4027 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4027 j) = 395527066 := by decide
private theorem lowerTwo_row_4028 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4028 j) = 397531865 := by decide
private theorem lowerTwo_row_4029 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4029 j) = 399231299 := by decide
private theorem lowerTwo_row_4030 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4030 j) = 401305453 := by decide
private theorem lowerTwo_row_4031 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4031 j) = 403026925 := by decide
private theorem lowerTwo_row_4032 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4032 j) = 405075813 := by decide
private theorem lowerTwo_row_4033 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4033 j) = 406867056 := by decide
private theorem lowerTwo_row_4034 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4034 j) = 408938571 := by decide
private theorem lowerTwo_row_4035 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4035 j) = 410704923 := by decide
private theorem lowerTwo_row_4036 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4036 j) = 412846877 := by decide
private theorem lowerTwo_row_4037 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4037 j) = 414635809 := by decide
private theorem lowerTwo_row_4038 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4038 j) = 416752529 := by decide
private theorem lowerTwo_row_4039 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4039 j) = 418611227 := by decide
private theorem lowerTwo_row_4040 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4040 j) = 420750473 := by decide
private theorem lowerTwo_row_4041 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4041 j) = 422584254 := by decide
private theorem lowerTwo_row_4042 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4042 j) = 424793940 := by decide
private theorem lowerTwo_row_4043 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4043 j) = 426650635 := by decide
private theorem lowerTwo_row_4044 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4044 j) = 428836033 := by decide
private theorem lowerTwo_row_4045 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4045 j) = 430763611 := by decide
private theorem lowerTwo_row_4046 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4046 j) = 432972578 := by decide
private theorem lowerTwo_row_4047 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4047 j) = 434876275 := by decide
private theorem lowerTwo_row_4048 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4048 j) = 437156801 := by decide
private theorem lowerTwo_row_4049 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4049 j) = 439084181 := by decide
private theorem lowerTwo_row_4050 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4050 j) = 441340603 := by decide
private theorem lowerTwo_row_4051 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4051 j) = 443338960 := by decide
private theorem lowerTwo_row_4052 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4052 j) = 445619078 := by decide
private theorem lowerTwo_row_4053 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4053 j) = 447593571 := by decide
private theorem lowerTwo_row_4054 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4054 j) = 449945334 := by decide
private theorem lowerTwo_row_4055 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4055 j) = 451944008 := by decide
private theorem lowerTwo_row_4056 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4056 j) = 454272575 := by decide
private theorem lowerTwo_row_4057 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4057 j) = 456343381 := by decide
private theorem lowerTwo_row_4058 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4058 j) = 458696839 := by decide
private theorem lowerTwo_row_4059 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4059 j) = 460744889 := by decide
private theorem lowerTwo_row_4060 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4060 j) = 463171181 := by decide
private theorem lowerTwo_row_4061 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4061 j) = 465244600 := by decide
private theorem lowerTwo_row_4062 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4062 j) = 467648865 := by decide
private theorem lowerTwo_row_4063 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4063 j) = 469795632 := by decide
private theorem lowerTwo_row_4064 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4064 j) = 472225199 := by decide
private theorem lowerTwo_row_4065 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4065 j) = 474348885 := by decide
private theorem lowerTwo_row_4066 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4066 j) = 476851069 := by decide
private theorem lowerTwo_row_4067 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4067 j) = 478999734 := by decide
private theorem lowerTwo_row_4068 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4068 j) = 481479400 := by decide
private theorem lowerTwo_row_4069 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4069 j) = 483701215 := by decide
private theorem lowerTwo_row_4070 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4070 j) = 486206575 := by decide
private theorem lowerTwo_row_4071 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4071 j) = 488406337 := by decide
private theorem lowerTwo_row_4072 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4072 j) = 490985648 := by decide
private theorem lowerTwo_row_4073 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4073 j) = 493211649 := by decide
private theorem lowerTwo_row_4074 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4074 j) = 495769649 := by decide
private theorem lowerTwo_row_4075 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4075 j) = 498070139 := by decide
private theorem lowerTwo_row_4076 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4076 j) = 500655141 := by decide
private theorem lowerTwo_row_4077 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4077 j) = 502934887 := by decide
private theorem lowerTwo_row_4078 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4078 j) = 505595166 := by decide
private theorem lowerTwo_row_4079 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4079 j) = 507902459 := by decide
private theorem lowerTwo_row_4080 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4080 j) = 510542804 := by decide
private theorem lowerTwo_row_4081 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4081 j) = 512926007 := by decide
private theorem lowerTwo_row_4082 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4082 j) = 515594702 := by decide
private theorem lowerTwo_row_4083 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4083 j) = 517958534 := by decide
private theorem lowerTwo_row_4084 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4084 j) = 520704004 := by decide
private theorem lowerTwo_row_4085 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4085 j) = 523096828 := by decide
private theorem lowerTwo_row_4086 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4086 j) = 525823739 := by decide
private theorem lowerTwo_row_4087 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4087 j) = 528293935 := by decide
private theorem lowerTwo_row_4088 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4088 j) = 531050757 := by decide
private theorem lowerTwo_row_4089 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4089 j) = 533503046 := by decide
private theorem lowerTwo_row_4090 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4090 j) = 536338145 := by decide
private theorem lowerTwo_row_4091 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4091 j) = 538821011 := by decide
private theorem lowerTwo_row_4092 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4092 j) = 541639060 := by decide
private theorem lowerTwo_row_4093 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4093 j) = 544200897 := by decide
private theorem lowerTwo_row_4094 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4094 j) = 547050495 := by decide
private theorem lowerTwo_row_4095 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4095 j) = 548868692 := by decide

/-- LEAF, OPEN. Page 51. The exact integer sum for the conservative E2 grid.
The full candidate kernel proof exceeded the bounded shift verification reserve.
The candidate is retained as text and is not proof evidence. This replaces the old E2 leaf. -/
theorem lower_two_grid_total : lowerTwoGridTotal = 1132433915806 := by
  show (∑ i ∈ Finset.range 4096, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight i j)
    = 1132433915806
  simp (config := { maxSteps := 4000000 }) only [
    lowerTwo_row_peel, lowerTwo_row_0, lowerTwo_row_1, lowerTwo_row_2, lowerTwo_row_3, lowerTwo_row_4, lowerTwo_row_5, lowerTwo_row_6, lowerTwo_row_7, lowerTwo_row_8, lowerTwo_row_9, lowerTwo_row_10, lowerTwo_row_11, lowerTwo_row_12, lowerTwo_row_13, lowerTwo_row_14, lowerTwo_row_15, lowerTwo_row_16, lowerTwo_row_17, lowerTwo_row_18, lowerTwo_row_19, lowerTwo_row_20, lowerTwo_row_21, lowerTwo_row_22, lowerTwo_row_23, lowerTwo_row_24, lowerTwo_row_25, lowerTwo_row_26, lowerTwo_row_27, lowerTwo_row_28, lowerTwo_row_29, lowerTwo_row_30,
    lowerTwo_row_31, lowerTwo_row_32, lowerTwo_row_33, lowerTwo_row_34, lowerTwo_row_35, lowerTwo_row_36, lowerTwo_row_37, lowerTwo_row_38, lowerTwo_row_39, lowerTwo_row_40, lowerTwo_row_41, lowerTwo_row_42, lowerTwo_row_43, lowerTwo_row_44, lowerTwo_row_45, lowerTwo_row_46, lowerTwo_row_47, lowerTwo_row_48, lowerTwo_row_49, lowerTwo_row_50, lowerTwo_row_51, lowerTwo_row_52, lowerTwo_row_53, lowerTwo_row_54, lowerTwo_row_55, lowerTwo_row_56, lowerTwo_row_57, lowerTwo_row_58, lowerTwo_row_59, lowerTwo_row_60, lowerTwo_row_61, lowerTwo_row_62,
    lowerTwo_row_63, lowerTwo_row_64, lowerTwo_row_65, lowerTwo_row_66, lowerTwo_row_67, lowerTwo_row_68, lowerTwo_row_69, lowerTwo_row_70, lowerTwo_row_71, lowerTwo_row_72, lowerTwo_row_73, lowerTwo_row_74, lowerTwo_row_75, lowerTwo_row_76, lowerTwo_row_77, lowerTwo_row_78, lowerTwo_row_79, lowerTwo_row_80, lowerTwo_row_81, lowerTwo_row_82, lowerTwo_row_83, lowerTwo_row_84, lowerTwo_row_85, lowerTwo_row_86, lowerTwo_row_87, lowerTwo_row_88, lowerTwo_row_89, lowerTwo_row_90, lowerTwo_row_91, lowerTwo_row_92, lowerTwo_row_93, lowerTwo_row_94,
    lowerTwo_row_95, lowerTwo_row_96, lowerTwo_row_97, lowerTwo_row_98, lowerTwo_row_99, lowerTwo_row_100, lowerTwo_row_101, lowerTwo_row_102, lowerTwo_row_103, lowerTwo_row_104, lowerTwo_row_105, lowerTwo_row_106, lowerTwo_row_107, lowerTwo_row_108, lowerTwo_row_109, lowerTwo_row_110, lowerTwo_row_111, lowerTwo_row_112, lowerTwo_row_113, lowerTwo_row_114, lowerTwo_row_115, lowerTwo_row_116, lowerTwo_row_117, lowerTwo_row_118, lowerTwo_row_119, lowerTwo_row_120, lowerTwo_row_121, lowerTwo_row_122, lowerTwo_row_123, lowerTwo_row_124, lowerTwo_row_125, lowerTwo_row_126,
    lowerTwo_row_127, lowerTwo_row_128, lowerTwo_row_129, lowerTwo_row_130, lowerTwo_row_131, lowerTwo_row_132, lowerTwo_row_133, lowerTwo_row_134, lowerTwo_row_135, lowerTwo_row_136, lowerTwo_row_137, lowerTwo_row_138, lowerTwo_row_139, lowerTwo_row_140, lowerTwo_row_141, lowerTwo_row_142, lowerTwo_row_143, lowerTwo_row_144, lowerTwo_row_145, lowerTwo_row_146, lowerTwo_row_147, lowerTwo_row_148, lowerTwo_row_149, lowerTwo_row_150, lowerTwo_row_151, lowerTwo_row_152, lowerTwo_row_153, lowerTwo_row_154, lowerTwo_row_155, lowerTwo_row_156, lowerTwo_row_157, lowerTwo_row_158,
    lowerTwo_row_159, lowerTwo_row_160, lowerTwo_row_161, lowerTwo_row_162, lowerTwo_row_163, lowerTwo_row_164, lowerTwo_row_165, lowerTwo_row_166, lowerTwo_row_167, lowerTwo_row_168, lowerTwo_row_169, lowerTwo_row_170, lowerTwo_row_171, lowerTwo_row_172, lowerTwo_row_173, lowerTwo_row_174, lowerTwo_row_175, lowerTwo_row_176, lowerTwo_row_177, lowerTwo_row_178, lowerTwo_row_179, lowerTwo_row_180, lowerTwo_row_181, lowerTwo_row_182, lowerTwo_row_183, lowerTwo_row_184, lowerTwo_row_185, lowerTwo_row_186, lowerTwo_row_187, lowerTwo_row_188, lowerTwo_row_189, lowerTwo_row_190,
    lowerTwo_row_191, lowerTwo_row_192, lowerTwo_row_193, lowerTwo_row_194, lowerTwo_row_195, lowerTwo_row_196, lowerTwo_row_197, lowerTwo_row_198, lowerTwo_row_199, lowerTwo_row_200, lowerTwo_row_201, lowerTwo_row_202, lowerTwo_row_203, lowerTwo_row_204, lowerTwo_row_205, lowerTwo_row_206, lowerTwo_row_207, lowerTwo_row_208, lowerTwo_row_209, lowerTwo_row_210, lowerTwo_row_211, lowerTwo_row_212, lowerTwo_row_213, lowerTwo_row_214, lowerTwo_row_215, lowerTwo_row_216, lowerTwo_row_217, lowerTwo_row_218, lowerTwo_row_219, lowerTwo_row_220, lowerTwo_row_221, lowerTwo_row_222,
    lowerTwo_row_223, lowerTwo_row_224, lowerTwo_row_225, lowerTwo_row_226, lowerTwo_row_227, lowerTwo_row_228, lowerTwo_row_229, lowerTwo_row_230, lowerTwo_row_231, lowerTwo_row_232, lowerTwo_row_233, lowerTwo_row_234, lowerTwo_row_235, lowerTwo_row_236, lowerTwo_row_237, lowerTwo_row_238, lowerTwo_row_239, lowerTwo_row_240, lowerTwo_row_241, lowerTwo_row_242, lowerTwo_row_243, lowerTwo_row_244, lowerTwo_row_245, lowerTwo_row_246, lowerTwo_row_247, lowerTwo_row_248, lowerTwo_row_249, lowerTwo_row_250, lowerTwo_row_251, lowerTwo_row_252, lowerTwo_row_253, lowerTwo_row_254,
    lowerTwo_row_255, lowerTwo_row_256, lowerTwo_row_257, lowerTwo_row_258, lowerTwo_row_259, lowerTwo_row_260, lowerTwo_row_261, lowerTwo_row_262, lowerTwo_row_263, lowerTwo_row_264, lowerTwo_row_265, lowerTwo_row_266, lowerTwo_row_267, lowerTwo_row_268, lowerTwo_row_269, lowerTwo_row_270, lowerTwo_row_271, lowerTwo_row_272, lowerTwo_row_273, lowerTwo_row_274, lowerTwo_row_275, lowerTwo_row_276, lowerTwo_row_277, lowerTwo_row_278, lowerTwo_row_279, lowerTwo_row_280, lowerTwo_row_281, lowerTwo_row_282, lowerTwo_row_283, lowerTwo_row_284, lowerTwo_row_285, lowerTwo_row_286,
    lowerTwo_row_287, lowerTwo_row_288, lowerTwo_row_289, lowerTwo_row_290, lowerTwo_row_291, lowerTwo_row_292, lowerTwo_row_293, lowerTwo_row_294, lowerTwo_row_295, lowerTwo_row_296, lowerTwo_row_297, lowerTwo_row_298, lowerTwo_row_299, lowerTwo_row_300, lowerTwo_row_301, lowerTwo_row_302, lowerTwo_row_303, lowerTwo_row_304, lowerTwo_row_305, lowerTwo_row_306, lowerTwo_row_307, lowerTwo_row_308, lowerTwo_row_309, lowerTwo_row_310, lowerTwo_row_311, lowerTwo_row_312, lowerTwo_row_313, lowerTwo_row_314, lowerTwo_row_315, lowerTwo_row_316, lowerTwo_row_317, lowerTwo_row_318,
    lowerTwo_row_319, lowerTwo_row_320, lowerTwo_row_321, lowerTwo_row_322, lowerTwo_row_323, lowerTwo_row_324, lowerTwo_row_325, lowerTwo_row_326, lowerTwo_row_327, lowerTwo_row_328, lowerTwo_row_329, lowerTwo_row_330, lowerTwo_row_331, lowerTwo_row_332, lowerTwo_row_333, lowerTwo_row_334, lowerTwo_row_335, lowerTwo_row_336, lowerTwo_row_337, lowerTwo_row_338, lowerTwo_row_339, lowerTwo_row_340, lowerTwo_row_341, lowerTwo_row_342, lowerTwo_row_343, lowerTwo_row_344, lowerTwo_row_345, lowerTwo_row_346, lowerTwo_row_347, lowerTwo_row_348, lowerTwo_row_349, lowerTwo_row_350,
    lowerTwo_row_351, lowerTwo_row_352, lowerTwo_row_353, lowerTwo_row_354, lowerTwo_row_355, lowerTwo_row_356, lowerTwo_row_357, lowerTwo_row_358, lowerTwo_row_359, lowerTwo_row_360, lowerTwo_row_361, lowerTwo_row_362, lowerTwo_row_363, lowerTwo_row_364, lowerTwo_row_365, lowerTwo_row_366, lowerTwo_row_367, lowerTwo_row_368, lowerTwo_row_369, lowerTwo_row_370, lowerTwo_row_371, lowerTwo_row_372, lowerTwo_row_373, lowerTwo_row_374, lowerTwo_row_375, lowerTwo_row_376, lowerTwo_row_377, lowerTwo_row_378, lowerTwo_row_379, lowerTwo_row_380, lowerTwo_row_381, lowerTwo_row_382,
    lowerTwo_row_383, lowerTwo_row_384, lowerTwo_row_385, lowerTwo_row_386, lowerTwo_row_387, lowerTwo_row_388, lowerTwo_row_389, lowerTwo_row_390, lowerTwo_row_391, lowerTwo_row_392, lowerTwo_row_393, lowerTwo_row_394, lowerTwo_row_395, lowerTwo_row_396, lowerTwo_row_397, lowerTwo_row_398, lowerTwo_row_399, lowerTwo_row_400, lowerTwo_row_401, lowerTwo_row_402, lowerTwo_row_403, lowerTwo_row_404, lowerTwo_row_405, lowerTwo_row_406, lowerTwo_row_407, lowerTwo_row_408, lowerTwo_row_409, lowerTwo_row_410, lowerTwo_row_411, lowerTwo_row_412, lowerTwo_row_413, lowerTwo_row_414,
    lowerTwo_row_415, lowerTwo_row_416, lowerTwo_row_417, lowerTwo_row_418, lowerTwo_row_419, lowerTwo_row_420, lowerTwo_row_421, lowerTwo_row_422, lowerTwo_row_423, lowerTwo_row_424, lowerTwo_row_425, lowerTwo_row_426, lowerTwo_row_427, lowerTwo_row_428, lowerTwo_row_429, lowerTwo_row_430, lowerTwo_row_431, lowerTwo_row_432, lowerTwo_row_433, lowerTwo_row_434, lowerTwo_row_435, lowerTwo_row_436, lowerTwo_row_437, lowerTwo_row_438, lowerTwo_row_439, lowerTwo_row_440, lowerTwo_row_441, lowerTwo_row_442, lowerTwo_row_443, lowerTwo_row_444, lowerTwo_row_445, lowerTwo_row_446,
    lowerTwo_row_447, lowerTwo_row_448, lowerTwo_row_449, lowerTwo_row_450, lowerTwo_row_451, lowerTwo_row_452, lowerTwo_row_453, lowerTwo_row_454, lowerTwo_row_455, lowerTwo_row_456, lowerTwo_row_457, lowerTwo_row_458, lowerTwo_row_459, lowerTwo_row_460, lowerTwo_row_461, lowerTwo_row_462, lowerTwo_row_463, lowerTwo_row_464, lowerTwo_row_465, lowerTwo_row_466, lowerTwo_row_467, lowerTwo_row_468, lowerTwo_row_469, lowerTwo_row_470, lowerTwo_row_471, lowerTwo_row_472, lowerTwo_row_473, lowerTwo_row_474, lowerTwo_row_475, lowerTwo_row_476, lowerTwo_row_477, lowerTwo_row_478,
    lowerTwo_row_479, lowerTwo_row_480, lowerTwo_row_481, lowerTwo_row_482, lowerTwo_row_483, lowerTwo_row_484, lowerTwo_row_485, lowerTwo_row_486, lowerTwo_row_487, lowerTwo_row_488, lowerTwo_row_489, lowerTwo_row_490, lowerTwo_row_491, lowerTwo_row_492, lowerTwo_row_493, lowerTwo_row_494, lowerTwo_row_495, lowerTwo_row_496, lowerTwo_row_497, lowerTwo_row_498, lowerTwo_row_499, lowerTwo_row_500, lowerTwo_row_501, lowerTwo_row_502, lowerTwo_row_503, lowerTwo_row_504, lowerTwo_row_505, lowerTwo_row_506, lowerTwo_row_507, lowerTwo_row_508, lowerTwo_row_509, lowerTwo_row_510,
    lowerTwo_row_511, lowerTwo_row_512, lowerTwo_row_513, lowerTwo_row_514, lowerTwo_row_515, lowerTwo_row_516, lowerTwo_row_517, lowerTwo_row_518, lowerTwo_row_519, lowerTwo_row_520, lowerTwo_row_521, lowerTwo_row_522, lowerTwo_row_523, lowerTwo_row_524, lowerTwo_row_525, lowerTwo_row_526, lowerTwo_row_527, lowerTwo_row_528, lowerTwo_row_529, lowerTwo_row_530, lowerTwo_row_531, lowerTwo_row_532, lowerTwo_row_533, lowerTwo_row_534, lowerTwo_row_535, lowerTwo_row_536, lowerTwo_row_537, lowerTwo_row_538, lowerTwo_row_539, lowerTwo_row_540, lowerTwo_row_541, lowerTwo_row_542,
    lowerTwo_row_543, lowerTwo_row_544, lowerTwo_row_545, lowerTwo_row_546, lowerTwo_row_547, lowerTwo_row_548, lowerTwo_row_549, lowerTwo_row_550, lowerTwo_row_551, lowerTwo_row_552, lowerTwo_row_553, lowerTwo_row_554, lowerTwo_row_555, lowerTwo_row_556, lowerTwo_row_557, lowerTwo_row_558, lowerTwo_row_559, lowerTwo_row_560, lowerTwo_row_561, lowerTwo_row_562, lowerTwo_row_563, lowerTwo_row_564, lowerTwo_row_565, lowerTwo_row_566, lowerTwo_row_567, lowerTwo_row_568, lowerTwo_row_569, lowerTwo_row_570, lowerTwo_row_571, lowerTwo_row_572, lowerTwo_row_573, lowerTwo_row_574,
    lowerTwo_row_575, lowerTwo_row_576, lowerTwo_row_577, lowerTwo_row_578, lowerTwo_row_579, lowerTwo_row_580, lowerTwo_row_581, lowerTwo_row_582, lowerTwo_row_583, lowerTwo_row_584, lowerTwo_row_585, lowerTwo_row_586, lowerTwo_row_587, lowerTwo_row_588, lowerTwo_row_589, lowerTwo_row_590, lowerTwo_row_591, lowerTwo_row_592, lowerTwo_row_593, lowerTwo_row_594, lowerTwo_row_595, lowerTwo_row_596, lowerTwo_row_597, lowerTwo_row_598, lowerTwo_row_599, lowerTwo_row_600, lowerTwo_row_601, lowerTwo_row_602, lowerTwo_row_603, lowerTwo_row_604, lowerTwo_row_605, lowerTwo_row_606,
    lowerTwo_row_607, lowerTwo_row_608, lowerTwo_row_609, lowerTwo_row_610, lowerTwo_row_611, lowerTwo_row_612, lowerTwo_row_613, lowerTwo_row_614, lowerTwo_row_615, lowerTwo_row_616, lowerTwo_row_617, lowerTwo_row_618, lowerTwo_row_619, lowerTwo_row_620, lowerTwo_row_621, lowerTwo_row_622, lowerTwo_row_623, lowerTwo_row_624, lowerTwo_row_625, lowerTwo_row_626, lowerTwo_row_627, lowerTwo_row_628, lowerTwo_row_629, lowerTwo_row_630, lowerTwo_row_631, lowerTwo_row_632, lowerTwo_row_633, lowerTwo_row_634, lowerTwo_row_635, lowerTwo_row_636, lowerTwo_row_637, lowerTwo_row_638,
    lowerTwo_row_639, lowerTwo_row_640, lowerTwo_row_641, lowerTwo_row_642, lowerTwo_row_643, lowerTwo_row_644, lowerTwo_row_645, lowerTwo_row_646, lowerTwo_row_647, lowerTwo_row_648, lowerTwo_row_649, lowerTwo_row_650, lowerTwo_row_651, lowerTwo_row_652, lowerTwo_row_653, lowerTwo_row_654, lowerTwo_row_655, lowerTwo_row_656, lowerTwo_row_657, lowerTwo_row_658, lowerTwo_row_659, lowerTwo_row_660, lowerTwo_row_661, lowerTwo_row_662, lowerTwo_row_663, lowerTwo_row_664, lowerTwo_row_665, lowerTwo_row_666, lowerTwo_row_667, lowerTwo_row_668, lowerTwo_row_669, lowerTwo_row_670,
    lowerTwo_row_671, lowerTwo_row_672, lowerTwo_row_673, lowerTwo_row_674, lowerTwo_row_675, lowerTwo_row_676, lowerTwo_row_677, lowerTwo_row_678, lowerTwo_row_679, lowerTwo_row_680, lowerTwo_row_681, lowerTwo_row_682, lowerTwo_row_683, lowerTwo_row_684, lowerTwo_row_685, lowerTwo_row_686, lowerTwo_row_687, lowerTwo_row_688, lowerTwo_row_689, lowerTwo_row_690, lowerTwo_row_691, lowerTwo_row_692, lowerTwo_row_693, lowerTwo_row_694, lowerTwo_row_695, lowerTwo_row_696, lowerTwo_row_697, lowerTwo_row_698, lowerTwo_row_699, lowerTwo_row_700, lowerTwo_row_701, lowerTwo_row_702,
    lowerTwo_row_703, lowerTwo_row_704, lowerTwo_row_705, lowerTwo_row_706, lowerTwo_row_707, lowerTwo_row_708, lowerTwo_row_709, lowerTwo_row_710, lowerTwo_row_711, lowerTwo_row_712, lowerTwo_row_713, lowerTwo_row_714, lowerTwo_row_715, lowerTwo_row_716, lowerTwo_row_717, lowerTwo_row_718, lowerTwo_row_719, lowerTwo_row_720, lowerTwo_row_721, lowerTwo_row_722, lowerTwo_row_723, lowerTwo_row_724, lowerTwo_row_725, lowerTwo_row_726, lowerTwo_row_727, lowerTwo_row_728, lowerTwo_row_729, lowerTwo_row_730, lowerTwo_row_731, lowerTwo_row_732, lowerTwo_row_733, lowerTwo_row_734,
    lowerTwo_row_735, lowerTwo_row_736, lowerTwo_row_737, lowerTwo_row_738, lowerTwo_row_739, lowerTwo_row_740, lowerTwo_row_741, lowerTwo_row_742, lowerTwo_row_743, lowerTwo_row_744, lowerTwo_row_745, lowerTwo_row_746, lowerTwo_row_747, lowerTwo_row_748, lowerTwo_row_749, lowerTwo_row_750, lowerTwo_row_751, lowerTwo_row_752, lowerTwo_row_753, lowerTwo_row_754, lowerTwo_row_755, lowerTwo_row_756, lowerTwo_row_757, lowerTwo_row_758, lowerTwo_row_759, lowerTwo_row_760, lowerTwo_row_761, lowerTwo_row_762, lowerTwo_row_763, lowerTwo_row_764, lowerTwo_row_765, lowerTwo_row_766,
    lowerTwo_row_767, lowerTwo_row_768, lowerTwo_row_769, lowerTwo_row_770, lowerTwo_row_771, lowerTwo_row_772, lowerTwo_row_773, lowerTwo_row_774, lowerTwo_row_775, lowerTwo_row_776, lowerTwo_row_777, lowerTwo_row_778, lowerTwo_row_779, lowerTwo_row_780, lowerTwo_row_781, lowerTwo_row_782, lowerTwo_row_783, lowerTwo_row_784, lowerTwo_row_785, lowerTwo_row_786, lowerTwo_row_787, lowerTwo_row_788, lowerTwo_row_789, lowerTwo_row_790, lowerTwo_row_791, lowerTwo_row_792, lowerTwo_row_793, lowerTwo_row_794, lowerTwo_row_795, lowerTwo_row_796, lowerTwo_row_797, lowerTwo_row_798,
    lowerTwo_row_799, lowerTwo_row_800, lowerTwo_row_801, lowerTwo_row_802, lowerTwo_row_803, lowerTwo_row_804, lowerTwo_row_805, lowerTwo_row_806, lowerTwo_row_807, lowerTwo_row_808, lowerTwo_row_809, lowerTwo_row_810, lowerTwo_row_811, lowerTwo_row_812, lowerTwo_row_813, lowerTwo_row_814, lowerTwo_row_815, lowerTwo_row_816, lowerTwo_row_817, lowerTwo_row_818, lowerTwo_row_819, lowerTwo_row_820, lowerTwo_row_821, lowerTwo_row_822, lowerTwo_row_823, lowerTwo_row_824, lowerTwo_row_825, lowerTwo_row_826, lowerTwo_row_827, lowerTwo_row_828, lowerTwo_row_829, lowerTwo_row_830,
    lowerTwo_row_831, lowerTwo_row_832, lowerTwo_row_833, lowerTwo_row_834, lowerTwo_row_835, lowerTwo_row_836, lowerTwo_row_837, lowerTwo_row_838, lowerTwo_row_839, lowerTwo_row_840, lowerTwo_row_841, lowerTwo_row_842, lowerTwo_row_843, lowerTwo_row_844, lowerTwo_row_845, lowerTwo_row_846, lowerTwo_row_847, lowerTwo_row_848, lowerTwo_row_849, lowerTwo_row_850, lowerTwo_row_851, lowerTwo_row_852, lowerTwo_row_853, lowerTwo_row_854, lowerTwo_row_855, lowerTwo_row_856, lowerTwo_row_857, lowerTwo_row_858, lowerTwo_row_859, lowerTwo_row_860, lowerTwo_row_861, lowerTwo_row_862,
    lowerTwo_row_863, lowerTwo_row_864, lowerTwo_row_865, lowerTwo_row_866, lowerTwo_row_867, lowerTwo_row_868, lowerTwo_row_869, lowerTwo_row_870, lowerTwo_row_871, lowerTwo_row_872, lowerTwo_row_873, lowerTwo_row_874, lowerTwo_row_875, lowerTwo_row_876, lowerTwo_row_877, lowerTwo_row_878, lowerTwo_row_879, lowerTwo_row_880, lowerTwo_row_881, lowerTwo_row_882, lowerTwo_row_883, lowerTwo_row_884, lowerTwo_row_885, lowerTwo_row_886, lowerTwo_row_887, lowerTwo_row_888, lowerTwo_row_889, lowerTwo_row_890, lowerTwo_row_891, lowerTwo_row_892, lowerTwo_row_893, lowerTwo_row_894,
    lowerTwo_row_895, lowerTwo_row_896, lowerTwo_row_897, lowerTwo_row_898, lowerTwo_row_899, lowerTwo_row_900, lowerTwo_row_901, lowerTwo_row_902, lowerTwo_row_903, lowerTwo_row_904, lowerTwo_row_905, lowerTwo_row_906, lowerTwo_row_907, lowerTwo_row_908, lowerTwo_row_909, lowerTwo_row_910, lowerTwo_row_911, lowerTwo_row_912, lowerTwo_row_913, lowerTwo_row_914, lowerTwo_row_915, lowerTwo_row_916, lowerTwo_row_917, lowerTwo_row_918, lowerTwo_row_919, lowerTwo_row_920, lowerTwo_row_921, lowerTwo_row_922, lowerTwo_row_923, lowerTwo_row_924, lowerTwo_row_925, lowerTwo_row_926,
    lowerTwo_row_927, lowerTwo_row_928, lowerTwo_row_929, lowerTwo_row_930, lowerTwo_row_931, lowerTwo_row_932, lowerTwo_row_933, lowerTwo_row_934, lowerTwo_row_935, lowerTwo_row_936, lowerTwo_row_937, lowerTwo_row_938, lowerTwo_row_939, lowerTwo_row_940, lowerTwo_row_941, lowerTwo_row_942, lowerTwo_row_943, lowerTwo_row_944, lowerTwo_row_945, lowerTwo_row_946, lowerTwo_row_947, lowerTwo_row_948, lowerTwo_row_949, lowerTwo_row_950, lowerTwo_row_951, lowerTwo_row_952, lowerTwo_row_953, lowerTwo_row_954, lowerTwo_row_955, lowerTwo_row_956, lowerTwo_row_957, lowerTwo_row_958,
    lowerTwo_row_959, lowerTwo_row_960, lowerTwo_row_961, lowerTwo_row_962, lowerTwo_row_963, lowerTwo_row_964, lowerTwo_row_965, lowerTwo_row_966, lowerTwo_row_967, lowerTwo_row_968, lowerTwo_row_969, lowerTwo_row_970, lowerTwo_row_971, lowerTwo_row_972, lowerTwo_row_973, lowerTwo_row_974, lowerTwo_row_975, lowerTwo_row_976, lowerTwo_row_977, lowerTwo_row_978, lowerTwo_row_979, lowerTwo_row_980, lowerTwo_row_981, lowerTwo_row_982, lowerTwo_row_983, lowerTwo_row_984, lowerTwo_row_985, lowerTwo_row_986, lowerTwo_row_987, lowerTwo_row_988, lowerTwo_row_989, lowerTwo_row_990,
    lowerTwo_row_991, lowerTwo_row_992, lowerTwo_row_993, lowerTwo_row_994, lowerTwo_row_995, lowerTwo_row_996, lowerTwo_row_997, lowerTwo_row_998, lowerTwo_row_999, lowerTwo_row_1000, lowerTwo_row_1001, lowerTwo_row_1002, lowerTwo_row_1003, lowerTwo_row_1004, lowerTwo_row_1005, lowerTwo_row_1006, lowerTwo_row_1007, lowerTwo_row_1008, lowerTwo_row_1009, lowerTwo_row_1010, lowerTwo_row_1011, lowerTwo_row_1012, lowerTwo_row_1013, lowerTwo_row_1014, lowerTwo_row_1015, lowerTwo_row_1016, lowerTwo_row_1017, lowerTwo_row_1018, lowerTwo_row_1019, lowerTwo_row_1020, lowerTwo_row_1021, lowerTwo_row_1022,
    lowerTwo_row_1023, lowerTwo_row_1024, lowerTwo_row_1025, lowerTwo_row_1026, lowerTwo_row_1027, lowerTwo_row_1028, lowerTwo_row_1029, lowerTwo_row_1030, lowerTwo_row_1031, lowerTwo_row_1032, lowerTwo_row_1033, lowerTwo_row_1034, lowerTwo_row_1035, lowerTwo_row_1036, lowerTwo_row_1037, lowerTwo_row_1038, lowerTwo_row_1039, lowerTwo_row_1040, lowerTwo_row_1041, lowerTwo_row_1042, lowerTwo_row_1043, lowerTwo_row_1044, lowerTwo_row_1045, lowerTwo_row_1046, lowerTwo_row_1047, lowerTwo_row_1048, lowerTwo_row_1049, lowerTwo_row_1050, lowerTwo_row_1051, lowerTwo_row_1052, lowerTwo_row_1053, lowerTwo_row_1054,
    lowerTwo_row_1055, lowerTwo_row_1056, lowerTwo_row_1057, lowerTwo_row_1058, lowerTwo_row_1059, lowerTwo_row_1060, lowerTwo_row_1061, lowerTwo_row_1062, lowerTwo_row_1063, lowerTwo_row_1064, lowerTwo_row_1065, lowerTwo_row_1066, lowerTwo_row_1067, lowerTwo_row_1068, lowerTwo_row_1069, lowerTwo_row_1070, lowerTwo_row_1071, lowerTwo_row_1072, lowerTwo_row_1073, lowerTwo_row_1074, lowerTwo_row_1075, lowerTwo_row_1076, lowerTwo_row_1077, lowerTwo_row_1078, lowerTwo_row_1079, lowerTwo_row_1080, lowerTwo_row_1081, lowerTwo_row_1082, lowerTwo_row_1083, lowerTwo_row_1084, lowerTwo_row_1085, lowerTwo_row_1086,
    lowerTwo_row_1087, lowerTwo_row_1088, lowerTwo_row_1089, lowerTwo_row_1090, lowerTwo_row_1091, lowerTwo_row_1092, lowerTwo_row_1093, lowerTwo_row_1094, lowerTwo_row_1095, lowerTwo_row_1096, lowerTwo_row_1097, lowerTwo_row_1098, lowerTwo_row_1099, lowerTwo_row_1100, lowerTwo_row_1101, lowerTwo_row_1102, lowerTwo_row_1103, lowerTwo_row_1104, lowerTwo_row_1105, lowerTwo_row_1106, lowerTwo_row_1107, lowerTwo_row_1108, lowerTwo_row_1109, lowerTwo_row_1110, lowerTwo_row_1111, lowerTwo_row_1112, lowerTwo_row_1113, lowerTwo_row_1114, lowerTwo_row_1115, lowerTwo_row_1116, lowerTwo_row_1117, lowerTwo_row_1118,
    lowerTwo_row_1119, lowerTwo_row_1120, lowerTwo_row_1121, lowerTwo_row_1122, lowerTwo_row_1123, lowerTwo_row_1124, lowerTwo_row_1125, lowerTwo_row_1126, lowerTwo_row_1127, lowerTwo_row_1128, lowerTwo_row_1129, lowerTwo_row_1130, lowerTwo_row_1131, lowerTwo_row_1132, lowerTwo_row_1133, lowerTwo_row_1134, lowerTwo_row_1135, lowerTwo_row_1136, lowerTwo_row_1137, lowerTwo_row_1138, lowerTwo_row_1139, lowerTwo_row_1140, lowerTwo_row_1141, lowerTwo_row_1142, lowerTwo_row_1143, lowerTwo_row_1144, lowerTwo_row_1145, lowerTwo_row_1146, lowerTwo_row_1147, lowerTwo_row_1148, lowerTwo_row_1149, lowerTwo_row_1150,
    lowerTwo_row_1151, lowerTwo_row_1152, lowerTwo_row_1153, lowerTwo_row_1154, lowerTwo_row_1155, lowerTwo_row_1156, lowerTwo_row_1157, lowerTwo_row_1158, lowerTwo_row_1159, lowerTwo_row_1160, lowerTwo_row_1161, lowerTwo_row_1162, lowerTwo_row_1163, lowerTwo_row_1164, lowerTwo_row_1165, lowerTwo_row_1166, lowerTwo_row_1167, lowerTwo_row_1168, lowerTwo_row_1169, lowerTwo_row_1170, lowerTwo_row_1171, lowerTwo_row_1172, lowerTwo_row_1173, lowerTwo_row_1174, lowerTwo_row_1175, lowerTwo_row_1176, lowerTwo_row_1177, lowerTwo_row_1178, lowerTwo_row_1179, lowerTwo_row_1180, lowerTwo_row_1181, lowerTwo_row_1182,
    lowerTwo_row_1183, lowerTwo_row_1184, lowerTwo_row_1185, lowerTwo_row_1186, lowerTwo_row_1187, lowerTwo_row_1188, lowerTwo_row_1189, lowerTwo_row_1190, lowerTwo_row_1191, lowerTwo_row_1192, lowerTwo_row_1193, lowerTwo_row_1194, lowerTwo_row_1195, lowerTwo_row_1196, lowerTwo_row_1197, lowerTwo_row_1198, lowerTwo_row_1199, lowerTwo_row_1200, lowerTwo_row_1201, lowerTwo_row_1202, lowerTwo_row_1203, lowerTwo_row_1204, lowerTwo_row_1205, lowerTwo_row_1206, lowerTwo_row_1207, lowerTwo_row_1208, lowerTwo_row_1209, lowerTwo_row_1210, lowerTwo_row_1211, lowerTwo_row_1212, lowerTwo_row_1213, lowerTwo_row_1214,
    lowerTwo_row_1215, lowerTwo_row_1216, lowerTwo_row_1217, lowerTwo_row_1218, lowerTwo_row_1219, lowerTwo_row_1220, lowerTwo_row_1221, lowerTwo_row_1222, lowerTwo_row_1223, lowerTwo_row_1224, lowerTwo_row_1225, lowerTwo_row_1226, lowerTwo_row_1227, lowerTwo_row_1228, lowerTwo_row_1229, lowerTwo_row_1230, lowerTwo_row_1231, lowerTwo_row_1232, lowerTwo_row_1233, lowerTwo_row_1234, lowerTwo_row_1235, lowerTwo_row_1236, lowerTwo_row_1237, lowerTwo_row_1238, lowerTwo_row_1239, lowerTwo_row_1240, lowerTwo_row_1241, lowerTwo_row_1242, lowerTwo_row_1243, lowerTwo_row_1244, lowerTwo_row_1245, lowerTwo_row_1246,
    lowerTwo_row_1247, lowerTwo_row_1248, lowerTwo_row_1249, lowerTwo_row_1250, lowerTwo_row_1251, lowerTwo_row_1252, lowerTwo_row_1253, lowerTwo_row_1254, lowerTwo_row_1255, lowerTwo_row_1256, lowerTwo_row_1257, lowerTwo_row_1258, lowerTwo_row_1259, lowerTwo_row_1260, lowerTwo_row_1261, lowerTwo_row_1262, lowerTwo_row_1263, lowerTwo_row_1264, lowerTwo_row_1265, lowerTwo_row_1266, lowerTwo_row_1267, lowerTwo_row_1268, lowerTwo_row_1269, lowerTwo_row_1270, lowerTwo_row_1271, lowerTwo_row_1272, lowerTwo_row_1273, lowerTwo_row_1274, lowerTwo_row_1275, lowerTwo_row_1276, lowerTwo_row_1277, lowerTwo_row_1278,
    lowerTwo_row_1279, lowerTwo_row_1280, lowerTwo_row_1281, lowerTwo_row_1282, lowerTwo_row_1283, lowerTwo_row_1284, lowerTwo_row_1285, lowerTwo_row_1286, lowerTwo_row_1287, lowerTwo_row_1288, lowerTwo_row_1289, lowerTwo_row_1290, lowerTwo_row_1291, lowerTwo_row_1292, lowerTwo_row_1293, lowerTwo_row_1294, lowerTwo_row_1295, lowerTwo_row_1296, lowerTwo_row_1297, lowerTwo_row_1298, lowerTwo_row_1299, lowerTwo_row_1300, lowerTwo_row_1301, lowerTwo_row_1302, lowerTwo_row_1303, lowerTwo_row_1304, lowerTwo_row_1305, lowerTwo_row_1306, lowerTwo_row_1307, lowerTwo_row_1308, lowerTwo_row_1309, lowerTwo_row_1310,
    lowerTwo_row_1311, lowerTwo_row_1312, lowerTwo_row_1313, lowerTwo_row_1314, lowerTwo_row_1315, lowerTwo_row_1316, lowerTwo_row_1317, lowerTwo_row_1318, lowerTwo_row_1319, lowerTwo_row_1320, lowerTwo_row_1321, lowerTwo_row_1322, lowerTwo_row_1323, lowerTwo_row_1324, lowerTwo_row_1325, lowerTwo_row_1326, lowerTwo_row_1327, lowerTwo_row_1328, lowerTwo_row_1329, lowerTwo_row_1330, lowerTwo_row_1331, lowerTwo_row_1332, lowerTwo_row_1333, lowerTwo_row_1334, lowerTwo_row_1335, lowerTwo_row_1336, lowerTwo_row_1337, lowerTwo_row_1338, lowerTwo_row_1339, lowerTwo_row_1340, lowerTwo_row_1341, lowerTwo_row_1342,
    lowerTwo_row_1343, lowerTwo_row_1344, lowerTwo_row_1345, lowerTwo_row_1346, lowerTwo_row_1347, lowerTwo_row_1348, lowerTwo_row_1349, lowerTwo_row_1350, lowerTwo_row_1351, lowerTwo_row_1352, lowerTwo_row_1353, lowerTwo_row_1354, lowerTwo_row_1355, lowerTwo_row_1356, lowerTwo_row_1357, lowerTwo_row_1358, lowerTwo_row_1359, lowerTwo_row_1360, lowerTwo_row_1361, lowerTwo_row_1362, lowerTwo_row_1363, lowerTwo_row_1364, lowerTwo_row_1365, lowerTwo_row_1366, lowerTwo_row_1367, lowerTwo_row_1368, lowerTwo_row_1369, lowerTwo_row_1370, lowerTwo_row_1371, lowerTwo_row_1372, lowerTwo_row_1373, lowerTwo_row_1374,
    lowerTwo_row_1375, lowerTwo_row_1376, lowerTwo_row_1377, lowerTwo_row_1378, lowerTwo_row_1379, lowerTwo_row_1380, lowerTwo_row_1381, lowerTwo_row_1382, lowerTwo_row_1383, lowerTwo_row_1384, lowerTwo_row_1385, lowerTwo_row_1386, lowerTwo_row_1387, lowerTwo_row_1388, lowerTwo_row_1389, lowerTwo_row_1390, lowerTwo_row_1391, lowerTwo_row_1392, lowerTwo_row_1393, lowerTwo_row_1394, lowerTwo_row_1395, lowerTwo_row_1396, lowerTwo_row_1397, lowerTwo_row_1398, lowerTwo_row_1399, lowerTwo_row_1400, lowerTwo_row_1401, lowerTwo_row_1402, lowerTwo_row_1403, lowerTwo_row_1404, lowerTwo_row_1405, lowerTwo_row_1406,
    lowerTwo_row_1407, lowerTwo_row_1408, lowerTwo_row_1409, lowerTwo_row_1410, lowerTwo_row_1411, lowerTwo_row_1412, lowerTwo_row_1413, lowerTwo_row_1414, lowerTwo_row_1415, lowerTwo_row_1416, lowerTwo_row_1417, lowerTwo_row_1418, lowerTwo_row_1419, lowerTwo_row_1420, lowerTwo_row_1421, lowerTwo_row_1422, lowerTwo_row_1423, lowerTwo_row_1424, lowerTwo_row_1425, lowerTwo_row_1426, lowerTwo_row_1427, lowerTwo_row_1428, lowerTwo_row_1429, lowerTwo_row_1430, lowerTwo_row_1431, lowerTwo_row_1432, lowerTwo_row_1433, lowerTwo_row_1434, lowerTwo_row_1435, lowerTwo_row_1436, lowerTwo_row_1437, lowerTwo_row_1438,
    lowerTwo_row_1439, lowerTwo_row_1440, lowerTwo_row_1441, lowerTwo_row_1442, lowerTwo_row_1443, lowerTwo_row_1444, lowerTwo_row_1445, lowerTwo_row_1446, lowerTwo_row_1447, lowerTwo_row_1448, lowerTwo_row_1449, lowerTwo_row_1450, lowerTwo_row_1451, lowerTwo_row_1452, lowerTwo_row_1453, lowerTwo_row_1454, lowerTwo_row_1455, lowerTwo_row_1456, lowerTwo_row_1457, lowerTwo_row_1458, lowerTwo_row_1459, lowerTwo_row_1460, lowerTwo_row_1461, lowerTwo_row_1462, lowerTwo_row_1463, lowerTwo_row_1464, lowerTwo_row_1465, lowerTwo_row_1466, lowerTwo_row_1467, lowerTwo_row_1468, lowerTwo_row_1469, lowerTwo_row_1470,
    lowerTwo_row_1471, lowerTwo_row_1472, lowerTwo_row_1473, lowerTwo_row_1474, lowerTwo_row_1475, lowerTwo_row_1476, lowerTwo_row_1477, lowerTwo_row_1478, lowerTwo_row_1479, lowerTwo_row_1480, lowerTwo_row_1481, lowerTwo_row_1482, lowerTwo_row_1483, lowerTwo_row_1484, lowerTwo_row_1485, lowerTwo_row_1486, lowerTwo_row_1487, lowerTwo_row_1488, lowerTwo_row_1489, lowerTwo_row_1490, lowerTwo_row_1491, lowerTwo_row_1492, lowerTwo_row_1493, lowerTwo_row_1494, lowerTwo_row_1495, lowerTwo_row_1496, lowerTwo_row_1497, lowerTwo_row_1498, lowerTwo_row_1499, lowerTwo_row_1500, lowerTwo_row_1501, lowerTwo_row_1502,
    lowerTwo_row_1503, lowerTwo_row_1504, lowerTwo_row_1505, lowerTwo_row_1506, lowerTwo_row_1507, lowerTwo_row_1508, lowerTwo_row_1509, lowerTwo_row_1510, lowerTwo_row_1511, lowerTwo_row_1512, lowerTwo_row_1513, lowerTwo_row_1514, lowerTwo_row_1515, lowerTwo_row_1516, lowerTwo_row_1517, lowerTwo_row_1518, lowerTwo_row_1519, lowerTwo_row_1520, lowerTwo_row_1521, lowerTwo_row_1522, lowerTwo_row_1523, lowerTwo_row_1524, lowerTwo_row_1525, lowerTwo_row_1526, lowerTwo_row_1527, lowerTwo_row_1528, lowerTwo_row_1529, lowerTwo_row_1530, lowerTwo_row_1531, lowerTwo_row_1532, lowerTwo_row_1533, lowerTwo_row_1534,
    lowerTwo_row_1535, lowerTwo_row_1536, lowerTwo_row_1537, lowerTwo_row_1538, lowerTwo_row_1539, lowerTwo_row_1540, lowerTwo_row_1541, lowerTwo_row_1542, lowerTwo_row_1543, lowerTwo_row_1544, lowerTwo_row_1545, lowerTwo_row_1546, lowerTwo_row_1547, lowerTwo_row_1548, lowerTwo_row_1549, lowerTwo_row_1550, lowerTwo_row_1551, lowerTwo_row_1552, lowerTwo_row_1553, lowerTwo_row_1554, lowerTwo_row_1555, lowerTwo_row_1556, lowerTwo_row_1557, lowerTwo_row_1558, lowerTwo_row_1559, lowerTwo_row_1560, lowerTwo_row_1561, lowerTwo_row_1562, lowerTwo_row_1563, lowerTwo_row_1564, lowerTwo_row_1565, lowerTwo_row_1566,
    lowerTwo_row_1567, lowerTwo_row_1568, lowerTwo_row_1569, lowerTwo_row_1570, lowerTwo_row_1571, lowerTwo_row_1572, lowerTwo_row_1573, lowerTwo_row_1574, lowerTwo_row_1575, lowerTwo_row_1576, lowerTwo_row_1577, lowerTwo_row_1578, lowerTwo_row_1579, lowerTwo_row_1580, lowerTwo_row_1581, lowerTwo_row_1582, lowerTwo_row_1583, lowerTwo_row_1584, lowerTwo_row_1585, lowerTwo_row_1586, lowerTwo_row_1587, lowerTwo_row_1588, lowerTwo_row_1589, lowerTwo_row_1590, lowerTwo_row_1591, lowerTwo_row_1592, lowerTwo_row_1593, lowerTwo_row_1594, lowerTwo_row_1595, lowerTwo_row_1596, lowerTwo_row_1597, lowerTwo_row_1598,
    lowerTwo_row_1599, lowerTwo_row_1600, lowerTwo_row_1601, lowerTwo_row_1602, lowerTwo_row_1603, lowerTwo_row_1604, lowerTwo_row_1605, lowerTwo_row_1606, lowerTwo_row_1607, lowerTwo_row_1608, lowerTwo_row_1609, lowerTwo_row_1610, lowerTwo_row_1611, lowerTwo_row_1612, lowerTwo_row_1613, lowerTwo_row_1614, lowerTwo_row_1615, lowerTwo_row_1616, lowerTwo_row_1617, lowerTwo_row_1618, lowerTwo_row_1619, lowerTwo_row_1620, lowerTwo_row_1621, lowerTwo_row_1622, lowerTwo_row_1623, lowerTwo_row_1624, lowerTwo_row_1625, lowerTwo_row_1626, lowerTwo_row_1627, lowerTwo_row_1628, lowerTwo_row_1629, lowerTwo_row_1630,
    lowerTwo_row_1631, lowerTwo_row_1632, lowerTwo_row_1633, lowerTwo_row_1634, lowerTwo_row_1635, lowerTwo_row_1636, lowerTwo_row_1637, lowerTwo_row_1638, lowerTwo_row_1639, lowerTwo_row_1640, lowerTwo_row_1641, lowerTwo_row_1642, lowerTwo_row_1643, lowerTwo_row_1644, lowerTwo_row_1645, lowerTwo_row_1646, lowerTwo_row_1647, lowerTwo_row_1648, lowerTwo_row_1649, lowerTwo_row_1650, lowerTwo_row_1651, lowerTwo_row_1652, lowerTwo_row_1653, lowerTwo_row_1654, lowerTwo_row_1655, lowerTwo_row_1656, lowerTwo_row_1657, lowerTwo_row_1658, lowerTwo_row_1659, lowerTwo_row_1660, lowerTwo_row_1661, lowerTwo_row_1662,
    lowerTwo_row_1663, lowerTwo_row_1664, lowerTwo_row_1665, lowerTwo_row_1666, lowerTwo_row_1667, lowerTwo_row_1668, lowerTwo_row_1669, lowerTwo_row_1670, lowerTwo_row_1671, lowerTwo_row_1672, lowerTwo_row_1673, lowerTwo_row_1674, lowerTwo_row_1675, lowerTwo_row_1676, lowerTwo_row_1677, lowerTwo_row_1678, lowerTwo_row_1679, lowerTwo_row_1680, lowerTwo_row_1681, lowerTwo_row_1682, lowerTwo_row_1683, lowerTwo_row_1684, lowerTwo_row_1685, lowerTwo_row_1686, lowerTwo_row_1687, lowerTwo_row_1688, lowerTwo_row_1689, lowerTwo_row_1690, lowerTwo_row_1691, lowerTwo_row_1692, lowerTwo_row_1693, lowerTwo_row_1694,
    lowerTwo_row_1695, lowerTwo_row_1696, lowerTwo_row_1697, lowerTwo_row_1698, lowerTwo_row_1699, lowerTwo_row_1700, lowerTwo_row_1701, lowerTwo_row_1702, lowerTwo_row_1703, lowerTwo_row_1704, lowerTwo_row_1705, lowerTwo_row_1706, lowerTwo_row_1707, lowerTwo_row_1708, lowerTwo_row_1709, lowerTwo_row_1710, lowerTwo_row_1711, lowerTwo_row_1712, lowerTwo_row_1713, lowerTwo_row_1714, lowerTwo_row_1715, lowerTwo_row_1716, lowerTwo_row_1717, lowerTwo_row_1718, lowerTwo_row_1719, lowerTwo_row_1720, lowerTwo_row_1721, lowerTwo_row_1722, lowerTwo_row_1723, lowerTwo_row_1724, lowerTwo_row_1725, lowerTwo_row_1726,
    lowerTwo_row_1727, lowerTwo_row_1728, lowerTwo_row_1729, lowerTwo_row_1730, lowerTwo_row_1731, lowerTwo_row_1732, lowerTwo_row_1733, lowerTwo_row_1734, lowerTwo_row_1735, lowerTwo_row_1736, lowerTwo_row_1737, lowerTwo_row_1738, lowerTwo_row_1739, lowerTwo_row_1740, lowerTwo_row_1741, lowerTwo_row_1742, lowerTwo_row_1743, lowerTwo_row_1744, lowerTwo_row_1745, lowerTwo_row_1746, lowerTwo_row_1747, lowerTwo_row_1748, lowerTwo_row_1749, lowerTwo_row_1750, lowerTwo_row_1751, lowerTwo_row_1752, lowerTwo_row_1753, lowerTwo_row_1754, lowerTwo_row_1755, lowerTwo_row_1756, lowerTwo_row_1757, lowerTwo_row_1758,
    lowerTwo_row_1759, lowerTwo_row_1760, lowerTwo_row_1761, lowerTwo_row_1762, lowerTwo_row_1763, lowerTwo_row_1764, lowerTwo_row_1765, lowerTwo_row_1766, lowerTwo_row_1767, lowerTwo_row_1768, lowerTwo_row_1769, lowerTwo_row_1770, lowerTwo_row_1771, lowerTwo_row_1772, lowerTwo_row_1773, lowerTwo_row_1774, lowerTwo_row_1775, lowerTwo_row_1776, lowerTwo_row_1777, lowerTwo_row_1778, lowerTwo_row_1779, lowerTwo_row_1780, lowerTwo_row_1781, lowerTwo_row_1782, lowerTwo_row_1783, lowerTwo_row_1784, lowerTwo_row_1785, lowerTwo_row_1786, lowerTwo_row_1787, lowerTwo_row_1788, lowerTwo_row_1789, lowerTwo_row_1790,
    lowerTwo_row_1791, lowerTwo_row_1792, lowerTwo_row_1793, lowerTwo_row_1794, lowerTwo_row_1795, lowerTwo_row_1796, lowerTwo_row_1797, lowerTwo_row_1798, lowerTwo_row_1799, lowerTwo_row_1800, lowerTwo_row_1801, lowerTwo_row_1802, lowerTwo_row_1803, lowerTwo_row_1804, lowerTwo_row_1805, lowerTwo_row_1806, lowerTwo_row_1807, lowerTwo_row_1808, lowerTwo_row_1809, lowerTwo_row_1810, lowerTwo_row_1811, lowerTwo_row_1812, lowerTwo_row_1813, lowerTwo_row_1814, lowerTwo_row_1815, lowerTwo_row_1816, lowerTwo_row_1817, lowerTwo_row_1818, lowerTwo_row_1819, lowerTwo_row_1820, lowerTwo_row_1821, lowerTwo_row_1822,
    lowerTwo_row_1823, lowerTwo_row_1824, lowerTwo_row_1825, lowerTwo_row_1826, lowerTwo_row_1827, lowerTwo_row_1828, lowerTwo_row_1829, lowerTwo_row_1830, lowerTwo_row_1831, lowerTwo_row_1832, lowerTwo_row_1833, lowerTwo_row_1834, lowerTwo_row_1835, lowerTwo_row_1836, lowerTwo_row_1837, lowerTwo_row_1838, lowerTwo_row_1839, lowerTwo_row_1840, lowerTwo_row_1841, lowerTwo_row_1842, lowerTwo_row_1843, lowerTwo_row_1844, lowerTwo_row_1845, lowerTwo_row_1846, lowerTwo_row_1847, lowerTwo_row_1848, lowerTwo_row_1849, lowerTwo_row_1850, lowerTwo_row_1851, lowerTwo_row_1852, lowerTwo_row_1853, lowerTwo_row_1854,
    lowerTwo_row_1855, lowerTwo_row_1856, lowerTwo_row_1857, lowerTwo_row_1858, lowerTwo_row_1859, lowerTwo_row_1860, lowerTwo_row_1861, lowerTwo_row_1862, lowerTwo_row_1863, lowerTwo_row_1864, lowerTwo_row_1865, lowerTwo_row_1866, lowerTwo_row_1867, lowerTwo_row_1868, lowerTwo_row_1869, lowerTwo_row_1870, lowerTwo_row_1871, lowerTwo_row_1872, lowerTwo_row_1873, lowerTwo_row_1874, lowerTwo_row_1875, lowerTwo_row_1876, lowerTwo_row_1877, lowerTwo_row_1878, lowerTwo_row_1879, lowerTwo_row_1880, lowerTwo_row_1881, lowerTwo_row_1882, lowerTwo_row_1883, lowerTwo_row_1884, lowerTwo_row_1885, lowerTwo_row_1886,
    lowerTwo_row_1887, lowerTwo_row_1888, lowerTwo_row_1889, lowerTwo_row_1890, lowerTwo_row_1891, lowerTwo_row_1892, lowerTwo_row_1893, lowerTwo_row_1894, lowerTwo_row_1895, lowerTwo_row_1896, lowerTwo_row_1897, lowerTwo_row_1898, lowerTwo_row_1899, lowerTwo_row_1900, lowerTwo_row_1901, lowerTwo_row_1902, lowerTwo_row_1903, lowerTwo_row_1904, lowerTwo_row_1905, lowerTwo_row_1906, lowerTwo_row_1907, lowerTwo_row_1908, lowerTwo_row_1909, lowerTwo_row_1910, lowerTwo_row_1911, lowerTwo_row_1912, lowerTwo_row_1913, lowerTwo_row_1914, lowerTwo_row_1915, lowerTwo_row_1916, lowerTwo_row_1917, lowerTwo_row_1918,
    lowerTwo_row_1919, lowerTwo_row_1920, lowerTwo_row_1921, lowerTwo_row_1922, lowerTwo_row_1923, lowerTwo_row_1924, lowerTwo_row_1925, lowerTwo_row_1926, lowerTwo_row_1927, lowerTwo_row_1928, lowerTwo_row_1929, lowerTwo_row_1930, lowerTwo_row_1931, lowerTwo_row_1932, lowerTwo_row_1933, lowerTwo_row_1934, lowerTwo_row_1935, lowerTwo_row_1936, lowerTwo_row_1937, lowerTwo_row_1938, lowerTwo_row_1939, lowerTwo_row_1940, lowerTwo_row_1941, lowerTwo_row_1942, lowerTwo_row_1943, lowerTwo_row_1944, lowerTwo_row_1945, lowerTwo_row_1946, lowerTwo_row_1947, lowerTwo_row_1948, lowerTwo_row_1949, lowerTwo_row_1950,
    lowerTwo_row_1951, lowerTwo_row_1952, lowerTwo_row_1953, lowerTwo_row_1954, lowerTwo_row_1955, lowerTwo_row_1956, lowerTwo_row_1957, lowerTwo_row_1958, lowerTwo_row_1959, lowerTwo_row_1960, lowerTwo_row_1961, lowerTwo_row_1962, lowerTwo_row_1963, lowerTwo_row_1964, lowerTwo_row_1965, lowerTwo_row_1966, lowerTwo_row_1967, lowerTwo_row_1968, lowerTwo_row_1969, lowerTwo_row_1970, lowerTwo_row_1971, lowerTwo_row_1972, lowerTwo_row_1973, lowerTwo_row_1974, lowerTwo_row_1975, lowerTwo_row_1976, lowerTwo_row_1977, lowerTwo_row_1978, lowerTwo_row_1979, lowerTwo_row_1980, lowerTwo_row_1981, lowerTwo_row_1982,
    lowerTwo_row_1983, lowerTwo_row_1984, lowerTwo_row_1985, lowerTwo_row_1986, lowerTwo_row_1987, lowerTwo_row_1988, lowerTwo_row_1989, lowerTwo_row_1990, lowerTwo_row_1991, lowerTwo_row_1992, lowerTwo_row_1993, lowerTwo_row_1994, lowerTwo_row_1995, lowerTwo_row_1996, lowerTwo_row_1997, lowerTwo_row_1998, lowerTwo_row_1999, lowerTwo_row_2000, lowerTwo_row_2001, lowerTwo_row_2002, lowerTwo_row_2003, lowerTwo_row_2004, lowerTwo_row_2005, lowerTwo_row_2006, lowerTwo_row_2007, lowerTwo_row_2008, lowerTwo_row_2009, lowerTwo_row_2010, lowerTwo_row_2011, lowerTwo_row_2012, lowerTwo_row_2013, lowerTwo_row_2014,
    lowerTwo_row_2015, lowerTwo_row_2016, lowerTwo_row_2017, lowerTwo_row_2018, lowerTwo_row_2019, lowerTwo_row_2020, lowerTwo_row_2021, lowerTwo_row_2022, lowerTwo_row_2023, lowerTwo_row_2024, lowerTwo_row_2025, lowerTwo_row_2026, lowerTwo_row_2027, lowerTwo_row_2028, lowerTwo_row_2029, lowerTwo_row_2030, lowerTwo_row_2031, lowerTwo_row_2032, lowerTwo_row_2033, lowerTwo_row_2034, lowerTwo_row_2035, lowerTwo_row_2036, lowerTwo_row_2037, lowerTwo_row_2038, lowerTwo_row_2039, lowerTwo_row_2040, lowerTwo_row_2041, lowerTwo_row_2042, lowerTwo_row_2043, lowerTwo_row_2044, lowerTwo_row_2045, lowerTwo_row_2046,
    lowerTwo_row_2047, lowerTwo_row_2048, lowerTwo_row_2049, lowerTwo_row_2050, lowerTwo_row_2051, lowerTwo_row_2052, lowerTwo_row_2053, lowerTwo_row_2054, lowerTwo_row_2055, lowerTwo_row_2056, lowerTwo_row_2057, lowerTwo_row_2058, lowerTwo_row_2059, lowerTwo_row_2060, lowerTwo_row_2061, lowerTwo_row_2062, lowerTwo_row_2063, lowerTwo_row_2064, lowerTwo_row_2065, lowerTwo_row_2066, lowerTwo_row_2067, lowerTwo_row_2068, lowerTwo_row_2069, lowerTwo_row_2070, lowerTwo_row_2071, lowerTwo_row_2072, lowerTwo_row_2073, lowerTwo_row_2074, lowerTwo_row_2075, lowerTwo_row_2076, lowerTwo_row_2077, lowerTwo_row_2078,
    lowerTwo_row_2079, lowerTwo_row_2080, lowerTwo_row_2081, lowerTwo_row_2082, lowerTwo_row_2083, lowerTwo_row_2084, lowerTwo_row_2085, lowerTwo_row_2086, lowerTwo_row_2087, lowerTwo_row_2088, lowerTwo_row_2089, lowerTwo_row_2090, lowerTwo_row_2091, lowerTwo_row_2092, lowerTwo_row_2093, lowerTwo_row_2094, lowerTwo_row_2095, lowerTwo_row_2096, lowerTwo_row_2097, lowerTwo_row_2098, lowerTwo_row_2099, lowerTwo_row_2100, lowerTwo_row_2101, lowerTwo_row_2102, lowerTwo_row_2103, lowerTwo_row_2104, lowerTwo_row_2105, lowerTwo_row_2106, lowerTwo_row_2107, lowerTwo_row_2108, lowerTwo_row_2109, lowerTwo_row_2110,
    lowerTwo_row_2111, lowerTwo_row_2112, lowerTwo_row_2113, lowerTwo_row_2114, lowerTwo_row_2115, lowerTwo_row_2116, lowerTwo_row_2117, lowerTwo_row_2118, lowerTwo_row_2119, lowerTwo_row_2120, lowerTwo_row_2121, lowerTwo_row_2122, lowerTwo_row_2123, lowerTwo_row_2124, lowerTwo_row_2125, lowerTwo_row_2126, lowerTwo_row_2127, lowerTwo_row_2128, lowerTwo_row_2129, lowerTwo_row_2130, lowerTwo_row_2131, lowerTwo_row_2132, lowerTwo_row_2133, lowerTwo_row_2134, lowerTwo_row_2135, lowerTwo_row_2136, lowerTwo_row_2137, lowerTwo_row_2138, lowerTwo_row_2139, lowerTwo_row_2140, lowerTwo_row_2141, lowerTwo_row_2142,
    lowerTwo_row_2143, lowerTwo_row_2144, lowerTwo_row_2145, lowerTwo_row_2146, lowerTwo_row_2147, lowerTwo_row_2148, lowerTwo_row_2149, lowerTwo_row_2150, lowerTwo_row_2151, lowerTwo_row_2152, lowerTwo_row_2153, lowerTwo_row_2154, lowerTwo_row_2155, lowerTwo_row_2156, lowerTwo_row_2157, lowerTwo_row_2158, lowerTwo_row_2159, lowerTwo_row_2160, lowerTwo_row_2161, lowerTwo_row_2162, lowerTwo_row_2163, lowerTwo_row_2164, lowerTwo_row_2165, lowerTwo_row_2166, lowerTwo_row_2167, lowerTwo_row_2168, lowerTwo_row_2169, lowerTwo_row_2170, lowerTwo_row_2171, lowerTwo_row_2172, lowerTwo_row_2173, lowerTwo_row_2174,
    lowerTwo_row_2175, lowerTwo_row_2176, lowerTwo_row_2177, lowerTwo_row_2178, lowerTwo_row_2179, lowerTwo_row_2180, lowerTwo_row_2181, lowerTwo_row_2182, lowerTwo_row_2183, lowerTwo_row_2184, lowerTwo_row_2185, lowerTwo_row_2186, lowerTwo_row_2187, lowerTwo_row_2188, lowerTwo_row_2189, lowerTwo_row_2190, lowerTwo_row_2191, lowerTwo_row_2192, lowerTwo_row_2193, lowerTwo_row_2194, lowerTwo_row_2195, lowerTwo_row_2196, lowerTwo_row_2197, lowerTwo_row_2198, lowerTwo_row_2199, lowerTwo_row_2200, lowerTwo_row_2201, lowerTwo_row_2202, lowerTwo_row_2203, lowerTwo_row_2204, lowerTwo_row_2205, lowerTwo_row_2206,
    lowerTwo_row_2207, lowerTwo_row_2208, lowerTwo_row_2209, lowerTwo_row_2210, lowerTwo_row_2211, lowerTwo_row_2212, lowerTwo_row_2213, lowerTwo_row_2214, lowerTwo_row_2215, lowerTwo_row_2216, lowerTwo_row_2217, lowerTwo_row_2218, lowerTwo_row_2219, lowerTwo_row_2220, lowerTwo_row_2221, lowerTwo_row_2222, lowerTwo_row_2223, lowerTwo_row_2224, lowerTwo_row_2225, lowerTwo_row_2226, lowerTwo_row_2227, lowerTwo_row_2228, lowerTwo_row_2229, lowerTwo_row_2230, lowerTwo_row_2231, lowerTwo_row_2232, lowerTwo_row_2233, lowerTwo_row_2234, lowerTwo_row_2235, lowerTwo_row_2236, lowerTwo_row_2237, lowerTwo_row_2238,
    lowerTwo_row_2239, lowerTwo_row_2240, lowerTwo_row_2241, lowerTwo_row_2242, lowerTwo_row_2243, lowerTwo_row_2244, lowerTwo_row_2245, lowerTwo_row_2246, lowerTwo_row_2247, lowerTwo_row_2248, lowerTwo_row_2249, lowerTwo_row_2250, lowerTwo_row_2251, lowerTwo_row_2252, lowerTwo_row_2253, lowerTwo_row_2254, lowerTwo_row_2255, lowerTwo_row_2256, lowerTwo_row_2257, lowerTwo_row_2258, lowerTwo_row_2259, lowerTwo_row_2260, lowerTwo_row_2261, lowerTwo_row_2262, lowerTwo_row_2263, lowerTwo_row_2264, lowerTwo_row_2265, lowerTwo_row_2266, lowerTwo_row_2267, lowerTwo_row_2268, lowerTwo_row_2269, lowerTwo_row_2270,
    lowerTwo_row_2271, lowerTwo_row_2272, lowerTwo_row_2273, lowerTwo_row_2274, lowerTwo_row_2275, lowerTwo_row_2276, lowerTwo_row_2277, lowerTwo_row_2278, lowerTwo_row_2279, lowerTwo_row_2280, lowerTwo_row_2281, lowerTwo_row_2282, lowerTwo_row_2283, lowerTwo_row_2284, lowerTwo_row_2285, lowerTwo_row_2286, lowerTwo_row_2287, lowerTwo_row_2288, lowerTwo_row_2289, lowerTwo_row_2290, lowerTwo_row_2291, lowerTwo_row_2292, lowerTwo_row_2293, lowerTwo_row_2294, lowerTwo_row_2295, lowerTwo_row_2296, lowerTwo_row_2297, lowerTwo_row_2298, lowerTwo_row_2299, lowerTwo_row_2300, lowerTwo_row_2301, lowerTwo_row_2302,
    lowerTwo_row_2303, lowerTwo_row_2304, lowerTwo_row_2305, lowerTwo_row_2306, lowerTwo_row_2307, lowerTwo_row_2308, lowerTwo_row_2309, lowerTwo_row_2310, lowerTwo_row_2311, lowerTwo_row_2312, lowerTwo_row_2313, lowerTwo_row_2314, lowerTwo_row_2315, lowerTwo_row_2316, lowerTwo_row_2317, lowerTwo_row_2318, lowerTwo_row_2319, lowerTwo_row_2320, lowerTwo_row_2321, lowerTwo_row_2322, lowerTwo_row_2323, lowerTwo_row_2324, lowerTwo_row_2325, lowerTwo_row_2326, lowerTwo_row_2327, lowerTwo_row_2328, lowerTwo_row_2329, lowerTwo_row_2330, lowerTwo_row_2331, lowerTwo_row_2332, lowerTwo_row_2333, lowerTwo_row_2334,
    lowerTwo_row_2335, lowerTwo_row_2336, lowerTwo_row_2337, lowerTwo_row_2338, lowerTwo_row_2339, lowerTwo_row_2340, lowerTwo_row_2341, lowerTwo_row_2342, lowerTwo_row_2343, lowerTwo_row_2344, lowerTwo_row_2345, lowerTwo_row_2346, lowerTwo_row_2347, lowerTwo_row_2348, lowerTwo_row_2349, lowerTwo_row_2350, lowerTwo_row_2351, lowerTwo_row_2352, lowerTwo_row_2353, lowerTwo_row_2354, lowerTwo_row_2355, lowerTwo_row_2356, lowerTwo_row_2357, lowerTwo_row_2358, lowerTwo_row_2359, lowerTwo_row_2360, lowerTwo_row_2361, lowerTwo_row_2362, lowerTwo_row_2363, lowerTwo_row_2364, lowerTwo_row_2365, lowerTwo_row_2366,
    lowerTwo_row_2367, lowerTwo_row_2368, lowerTwo_row_2369, lowerTwo_row_2370, lowerTwo_row_2371, lowerTwo_row_2372, lowerTwo_row_2373, lowerTwo_row_2374, lowerTwo_row_2375, lowerTwo_row_2376, lowerTwo_row_2377, lowerTwo_row_2378, lowerTwo_row_2379, lowerTwo_row_2380, lowerTwo_row_2381, lowerTwo_row_2382, lowerTwo_row_2383, lowerTwo_row_2384, lowerTwo_row_2385, lowerTwo_row_2386, lowerTwo_row_2387, lowerTwo_row_2388, lowerTwo_row_2389, lowerTwo_row_2390, lowerTwo_row_2391, lowerTwo_row_2392, lowerTwo_row_2393, lowerTwo_row_2394, lowerTwo_row_2395, lowerTwo_row_2396, lowerTwo_row_2397, lowerTwo_row_2398,
    lowerTwo_row_2399, lowerTwo_row_2400, lowerTwo_row_2401, lowerTwo_row_2402, lowerTwo_row_2403, lowerTwo_row_2404, lowerTwo_row_2405, lowerTwo_row_2406, lowerTwo_row_2407, lowerTwo_row_2408, lowerTwo_row_2409, lowerTwo_row_2410, lowerTwo_row_2411, lowerTwo_row_2412, lowerTwo_row_2413, lowerTwo_row_2414, lowerTwo_row_2415, lowerTwo_row_2416, lowerTwo_row_2417, lowerTwo_row_2418, lowerTwo_row_2419, lowerTwo_row_2420, lowerTwo_row_2421, lowerTwo_row_2422, lowerTwo_row_2423, lowerTwo_row_2424, lowerTwo_row_2425, lowerTwo_row_2426, lowerTwo_row_2427, lowerTwo_row_2428, lowerTwo_row_2429, lowerTwo_row_2430,
    lowerTwo_row_2431, lowerTwo_row_2432, lowerTwo_row_2433, lowerTwo_row_2434, lowerTwo_row_2435, lowerTwo_row_2436, lowerTwo_row_2437, lowerTwo_row_2438, lowerTwo_row_2439, lowerTwo_row_2440, lowerTwo_row_2441, lowerTwo_row_2442, lowerTwo_row_2443, lowerTwo_row_2444, lowerTwo_row_2445, lowerTwo_row_2446, lowerTwo_row_2447, lowerTwo_row_2448, lowerTwo_row_2449, lowerTwo_row_2450, lowerTwo_row_2451, lowerTwo_row_2452, lowerTwo_row_2453, lowerTwo_row_2454, lowerTwo_row_2455, lowerTwo_row_2456, lowerTwo_row_2457, lowerTwo_row_2458, lowerTwo_row_2459, lowerTwo_row_2460, lowerTwo_row_2461, lowerTwo_row_2462,
    lowerTwo_row_2463, lowerTwo_row_2464, lowerTwo_row_2465, lowerTwo_row_2466, lowerTwo_row_2467, lowerTwo_row_2468, lowerTwo_row_2469, lowerTwo_row_2470, lowerTwo_row_2471, lowerTwo_row_2472, lowerTwo_row_2473, lowerTwo_row_2474, lowerTwo_row_2475, lowerTwo_row_2476, lowerTwo_row_2477, lowerTwo_row_2478, lowerTwo_row_2479, lowerTwo_row_2480, lowerTwo_row_2481, lowerTwo_row_2482, lowerTwo_row_2483, lowerTwo_row_2484, lowerTwo_row_2485, lowerTwo_row_2486, lowerTwo_row_2487, lowerTwo_row_2488, lowerTwo_row_2489, lowerTwo_row_2490, lowerTwo_row_2491, lowerTwo_row_2492, lowerTwo_row_2493, lowerTwo_row_2494,
    lowerTwo_row_2495, lowerTwo_row_2496, lowerTwo_row_2497, lowerTwo_row_2498, lowerTwo_row_2499, lowerTwo_row_2500, lowerTwo_row_2501, lowerTwo_row_2502, lowerTwo_row_2503, lowerTwo_row_2504, lowerTwo_row_2505, lowerTwo_row_2506, lowerTwo_row_2507, lowerTwo_row_2508, lowerTwo_row_2509, lowerTwo_row_2510, lowerTwo_row_2511, lowerTwo_row_2512, lowerTwo_row_2513, lowerTwo_row_2514, lowerTwo_row_2515, lowerTwo_row_2516, lowerTwo_row_2517, lowerTwo_row_2518, lowerTwo_row_2519, lowerTwo_row_2520, lowerTwo_row_2521, lowerTwo_row_2522, lowerTwo_row_2523, lowerTwo_row_2524, lowerTwo_row_2525, lowerTwo_row_2526,
    lowerTwo_row_2527, lowerTwo_row_2528, lowerTwo_row_2529, lowerTwo_row_2530, lowerTwo_row_2531, lowerTwo_row_2532, lowerTwo_row_2533, lowerTwo_row_2534, lowerTwo_row_2535, lowerTwo_row_2536, lowerTwo_row_2537, lowerTwo_row_2538, lowerTwo_row_2539, lowerTwo_row_2540, lowerTwo_row_2541, lowerTwo_row_2542, lowerTwo_row_2543, lowerTwo_row_2544, lowerTwo_row_2545, lowerTwo_row_2546, lowerTwo_row_2547, lowerTwo_row_2548, lowerTwo_row_2549, lowerTwo_row_2550, lowerTwo_row_2551, lowerTwo_row_2552, lowerTwo_row_2553, lowerTwo_row_2554, lowerTwo_row_2555, lowerTwo_row_2556, lowerTwo_row_2557, lowerTwo_row_2558,
    lowerTwo_row_2559, lowerTwo_row_2560, lowerTwo_row_2561, lowerTwo_row_2562, lowerTwo_row_2563, lowerTwo_row_2564, lowerTwo_row_2565, lowerTwo_row_2566, lowerTwo_row_2567, lowerTwo_row_2568, lowerTwo_row_2569, lowerTwo_row_2570, lowerTwo_row_2571, lowerTwo_row_2572, lowerTwo_row_2573, lowerTwo_row_2574, lowerTwo_row_2575, lowerTwo_row_2576, lowerTwo_row_2577, lowerTwo_row_2578, lowerTwo_row_2579, lowerTwo_row_2580, lowerTwo_row_2581, lowerTwo_row_2582, lowerTwo_row_2583, lowerTwo_row_2584, lowerTwo_row_2585, lowerTwo_row_2586, lowerTwo_row_2587, lowerTwo_row_2588, lowerTwo_row_2589, lowerTwo_row_2590,
    lowerTwo_row_2591, lowerTwo_row_2592, lowerTwo_row_2593, lowerTwo_row_2594, lowerTwo_row_2595, lowerTwo_row_2596, lowerTwo_row_2597, lowerTwo_row_2598, lowerTwo_row_2599, lowerTwo_row_2600, lowerTwo_row_2601, lowerTwo_row_2602, lowerTwo_row_2603, lowerTwo_row_2604, lowerTwo_row_2605, lowerTwo_row_2606, lowerTwo_row_2607, lowerTwo_row_2608, lowerTwo_row_2609, lowerTwo_row_2610, lowerTwo_row_2611, lowerTwo_row_2612, lowerTwo_row_2613, lowerTwo_row_2614, lowerTwo_row_2615, lowerTwo_row_2616, lowerTwo_row_2617, lowerTwo_row_2618, lowerTwo_row_2619, lowerTwo_row_2620, lowerTwo_row_2621, lowerTwo_row_2622,
    lowerTwo_row_2623, lowerTwo_row_2624, lowerTwo_row_2625, lowerTwo_row_2626, lowerTwo_row_2627, lowerTwo_row_2628, lowerTwo_row_2629, lowerTwo_row_2630, lowerTwo_row_2631, lowerTwo_row_2632, lowerTwo_row_2633, lowerTwo_row_2634, lowerTwo_row_2635, lowerTwo_row_2636, lowerTwo_row_2637, lowerTwo_row_2638, lowerTwo_row_2639, lowerTwo_row_2640, lowerTwo_row_2641, lowerTwo_row_2642, lowerTwo_row_2643, lowerTwo_row_2644, lowerTwo_row_2645, lowerTwo_row_2646, lowerTwo_row_2647, lowerTwo_row_2648, lowerTwo_row_2649, lowerTwo_row_2650, lowerTwo_row_2651, lowerTwo_row_2652, lowerTwo_row_2653, lowerTwo_row_2654,
    lowerTwo_row_2655, lowerTwo_row_2656, lowerTwo_row_2657, lowerTwo_row_2658, lowerTwo_row_2659, lowerTwo_row_2660, lowerTwo_row_2661, lowerTwo_row_2662, lowerTwo_row_2663, lowerTwo_row_2664, lowerTwo_row_2665, lowerTwo_row_2666, lowerTwo_row_2667, lowerTwo_row_2668, lowerTwo_row_2669, lowerTwo_row_2670, lowerTwo_row_2671, lowerTwo_row_2672, lowerTwo_row_2673, lowerTwo_row_2674, lowerTwo_row_2675, lowerTwo_row_2676, lowerTwo_row_2677, lowerTwo_row_2678, lowerTwo_row_2679, lowerTwo_row_2680, lowerTwo_row_2681, lowerTwo_row_2682, lowerTwo_row_2683, lowerTwo_row_2684, lowerTwo_row_2685, lowerTwo_row_2686,
    lowerTwo_row_2687, lowerTwo_row_2688, lowerTwo_row_2689, lowerTwo_row_2690, lowerTwo_row_2691, lowerTwo_row_2692, lowerTwo_row_2693, lowerTwo_row_2694, lowerTwo_row_2695, lowerTwo_row_2696, lowerTwo_row_2697, lowerTwo_row_2698, lowerTwo_row_2699, lowerTwo_row_2700, lowerTwo_row_2701, lowerTwo_row_2702, lowerTwo_row_2703, lowerTwo_row_2704, lowerTwo_row_2705, lowerTwo_row_2706, lowerTwo_row_2707, lowerTwo_row_2708, lowerTwo_row_2709, lowerTwo_row_2710, lowerTwo_row_2711, lowerTwo_row_2712, lowerTwo_row_2713, lowerTwo_row_2714, lowerTwo_row_2715, lowerTwo_row_2716, lowerTwo_row_2717, lowerTwo_row_2718,
    lowerTwo_row_2719, lowerTwo_row_2720, lowerTwo_row_2721, lowerTwo_row_2722, lowerTwo_row_2723, lowerTwo_row_2724, lowerTwo_row_2725, lowerTwo_row_2726, lowerTwo_row_2727, lowerTwo_row_2728, lowerTwo_row_2729, lowerTwo_row_2730, lowerTwo_row_2731, lowerTwo_row_2732, lowerTwo_row_2733, lowerTwo_row_2734, lowerTwo_row_2735, lowerTwo_row_2736, lowerTwo_row_2737, lowerTwo_row_2738, lowerTwo_row_2739, lowerTwo_row_2740, lowerTwo_row_2741, lowerTwo_row_2742, lowerTwo_row_2743, lowerTwo_row_2744, lowerTwo_row_2745, lowerTwo_row_2746, lowerTwo_row_2747, lowerTwo_row_2748, lowerTwo_row_2749, lowerTwo_row_2750,
    lowerTwo_row_2751, lowerTwo_row_2752, lowerTwo_row_2753, lowerTwo_row_2754, lowerTwo_row_2755, lowerTwo_row_2756, lowerTwo_row_2757, lowerTwo_row_2758, lowerTwo_row_2759, lowerTwo_row_2760, lowerTwo_row_2761, lowerTwo_row_2762, lowerTwo_row_2763, lowerTwo_row_2764, lowerTwo_row_2765, lowerTwo_row_2766, lowerTwo_row_2767, lowerTwo_row_2768, lowerTwo_row_2769, lowerTwo_row_2770, lowerTwo_row_2771, lowerTwo_row_2772, lowerTwo_row_2773, lowerTwo_row_2774, lowerTwo_row_2775, lowerTwo_row_2776, lowerTwo_row_2777, lowerTwo_row_2778, lowerTwo_row_2779, lowerTwo_row_2780, lowerTwo_row_2781, lowerTwo_row_2782,
    lowerTwo_row_2783, lowerTwo_row_2784, lowerTwo_row_2785, lowerTwo_row_2786, lowerTwo_row_2787, lowerTwo_row_2788, lowerTwo_row_2789, lowerTwo_row_2790, lowerTwo_row_2791, lowerTwo_row_2792, lowerTwo_row_2793, lowerTwo_row_2794, lowerTwo_row_2795, lowerTwo_row_2796, lowerTwo_row_2797, lowerTwo_row_2798, lowerTwo_row_2799, lowerTwo_row_2800, lowerTwo_row_2801, lowerTwo_row_2802, lowerTwo_row_2803, lowerTwo_row_2804, lowerTwo_row_2805, lowerTwo_row_2806, lowerTwo_row_2807, lowerTwo_row_2808, lowerTwo_row_2809, lowerTwo_row_2810, lowerTwo_row_2811, lowerTwo_row_2812, lowerTwo_row_2813, lowerTwo_row_2814,
    lowerTwo_row_2815, lowerTwo_row_2816, lowerTwo_row_2817, lowerTwo_row_2818, lowerTwo_row_2819, lowerTwo_row_2820, lowerTwo_row_2821, lowerTwo_row_2822, lowerTwo_row_2823, lowerTwo_row_2824, lowerTwo_row_2825, lowerTwo_row_2826, lowerTwo_row_2827, lowerTwo_row_2828, lowerTwo_row_2829, lowerTwo_row_2830, lowerTwo_row_2831, lowerTwo_row_2832, lowerTwo_row_2833, lowerTwo_row_2834, lowerTwo_row_2835, lowerTwo_row_2836, lowerTwo_row_2837, lowerTwo_row_2838, lowerTwo_row_2839, lowerTwo_row_2840, lowerTwo_row_2841, lowerTwo_row_2842, lowerTwo_row_2843, lowerTwo_row_2844, lowerTwo_row_2845, lowerTwo_row_2846,
    lowerTwo_row_2847, lowerTwo_row_2848, lowerTwo_row_2849, lowerTwo_row_2850, lowerTwo_row_2851, lowerTwo_row_2852, lowerTwo_row_2853, lowerTwo_row_2854, lowerTwo_row_2855, lowerTwo_row_2856, lowerTwo_row_2857, lowerTwo_row_2858, lowerTwo_row_2859, lowerTwo_row_2860, lowerTwo_row_2861, lowerTwo_row_2862, lowerTwo_row_2863, lowerTwo_row_2864, lowerTwo_row_2865, lowerTwo_row_2866, lowerTwo_row_2867, lowerTwo_row_2868, lowerTwo_row_2869, lowerTwo_row_2870, lowerTwo_row_2871, lowerTwo_row_2872, lowerTwo_row_2873, lowerTwo_row_2874, lowerTwo_row_2875, lowerTwo_row_2876, lowerTwo_row_2877, lowerTwo_row_2878,
    lowerTwo_row_2879, lowerTwo_row_2880, lowerTwo_row_2881, lowerTwo_row_2882, lowerTwo_row_2883, lowerTwo_row_2884, lowerTwo_row_2885, lowerTwo_row_2886, lowerTwo_row_2887, lowerTwo_row_2888, lowerTwo_row_2889, lowerTwo_row_2890, lowerTwo_row_2891, lowerTwo_row_2892, lowerTwo_row_2893, lowerTwo_row_2894, lowerTwo_row_2895, lowerTwo_row_2896, lowerTwo_row_2897, lowerTwo_row_2898, lowerTwo_row_2899, lowerTwo_row_2900, lowerTwo_row_2901, lowerTwo_row_2902, lowerTwo_row_2903, lowerTwo_row_2904, lowerTwo_row_2905, lowerTwo_row_2906, lowerTwo_row_2907, lowerTwo_row_2908, lowerTwo_row_2909, lowerTwo_row_2910,
    lowerTwo_row_2911, lowerTwo_row_2912, lowerTwo_row_2913, lowerTwo_row_2914, lowerTwo_row_2915, lowerTwo_row_2916, lowerTwo_row_2917, lowerTwo_row_2918, lowerTwo_row_2919, lowerTwo_row_2920, lowerTwo_row_2921, lowerTwo_row_2922, lowerTwo_row_2923, lowerTwo_row_2924, lowerTwo_row_2925, lowerTwo_row_2926, lowerTwo_row_2927, lowerTwo_row_2928, lowerTwo_row_2929, lowerTwo_row_2930, lowerTwo_row_2931, lowerTwo_row_2932, lowerTwo_row_2933, lowerTwo_row_2934, lowerTwo_row_2935, lowerTwo_row_2936, lowerTwo_row_2937, lowerTwo_row_2938, lowerTwo_row_2939, lowerTwo_row_2940, lowerTwo_row_2941, lowerTwo_row_2942,
    lowerTwo_row_2943, lowerTwo_row_2944, lowerTwo_row_2945, lowerTwo_row_2946, lowerTwo_row_2947, lowerTwo_row_2948, lowerTwo_row_2949, lowerTwo_row_2950, lowerTwo_row_2951, lowerTwo_row_2952, lowerTwo_row_2953, lowerTwo_row_2954, lowerTwo_row_2955, lowerTwo_row_2956, lowerTwo_row_2957, lowerTwo_row_2958, lowerTwo_row_2959, lowerTwo_row_2960, lowerTwo_row_2961, lowerTwo_row_2962, lowerTwo_row_2963, lowerTwo_row_2964, lowerTwo_row_2965, lowerTwo_row_2966, lowerTwo_row_2967, lowerTwo_row_2968, lowerTwo_row_2969, lowerTwo_row_2970, lowerTwo_row_2971, lowerTwo_row_2972, lowerTwo_row_2973, lowerTwo_row_2974,
    lowerTwo_row_2975, lowerTwo_row_2976, lowerTwo_row_2977, lowerTwo_row_2978, lowerTwo_row_2979, lowerTwo_row_2980, lowerTwo_row_2981, lowerTwo_row_2982, lowerTwo_row_2983, lowerTwo_row_2984, lowerTwo_row_2985, lowerTwo_row_2986, lowerTwo_row_2987, lowerTwo_row_2988, lowerTwo_row_2989, lowerTwo_row_2990, lowerTwo_row_2991, lowerTwo_row_2992, lowerTwo_row_2993, lowerTwo_row_2994, lowerTwo_row_2995, lowerTwo_row_2996, lowerTwo_row_2997, lowerTwo_row_2998, lowerTwo_row_2999, lowerTwo_row_3000, lowerTwo_row_3001, lowerTwo_row_3002, lowerTwo_row_3003, lowerTwo_row_3004, lowerTwo_row_3005, lowerTwo_row_3006,
    lowerTwo_row_3007, lowerTwo_row_3008, lowerTwo_row_3009, lowerTwo_row_3010, lowerTwo_row_3011, lowerTwo_row_3012, lowerTwo_row_3013, lowerTwo_row_3014, lowerTwo_row_3015, lowerTwo_row_3016, lowerTwo_row_3017, lowerTwo_row_3018, lowerTwo_row_3019, lowerTwo_row_3020, lowerTwo_row_3021, lowerTwo_row_3022, lowerTwo_row_3023, lowerTwo_row_3024, lowerTwo_row_3025, lowerTwo_row_3026, lowerTwo_row_3027, lowerTwo_row_3028, lowerTwo_row_3029, lowerTwo_row_3030, lowerTwo_row_3031, lowerTwo_row_3032, lowerTwo_row_3033, lowerTwo_row_3034, lowerTwo_row_3035, lowerTwo_row_3036, lowerTwo_row_3037, lowerTwo_row_3038,
    lowerTwo_row_3039, lowerTwo_row_3040, lowerTwo_row_3041, lowerTwo_row_3042, lowerTwo_row_3043, lowerTwo_row_3044, lowerTwo_row_3045, lowerTwo_row_3046, lowerTwo_row_3047, lowerTwo_row_3048, lowerTwo_row_3049, lowerTwo_row_3050, lowerTwo_row_3051, lowerTwo_row_3052, lowerTwo_row_3053, lowerTwo_row_3054, lowerTwo_row_3055, lowerTwo_row_3056, lowerTwo_row_3057, lowerTwo_row_3058, lowerTwo_row_3059, lowerTwo_row_3060, lowerTwo_row_3061, lowerTwo_row_3062, lowerTwo_row_3063, lowerTwo_row_3064, lowerTwo_row_3065, lowerTwo_row_3066, lowerTwo_row_3067, lowerTwo_row_3068, lowerTwo_row_3069, lowerTwo_row_3070,
    lowerTwo_row_3071, lowerTwo_row_3072, lowerTwo_row_3073, lowerTwo_row_3074, lowerTwo_row_3075, lowerTwo_row_3076, lowerTwo_row_3077, lowerTwo_row_3078, lowerTwo_row_3079, lowerTwo_row_3080, lowerTwo_row_3081, lowerTwo_row_3082, lowerTwo_row_3083, lowerTwo_row_3084, lowerTwo_row_3085, lowerTwo_row_3086, lowerTwo_row_3087, lowerTwo_row_3088, lowerTwo_row_3089, lowerTwo_row_3090, lowerTwo_row_3091, lowerTwo_row_3092, lowerTwo_row_3093, lowerTwo_row_3094, lowerTwo_row_3095, lowerTwo_row_3096, lowerTwo_row_3097, lowerTwo_row_3098, lowerTwo_row_3099, lowerTwo_row_3100, lowerTwo_row_3101, lowerTwo_row_3102,
    lowerTwo_row_3103, lowerTwo_row_3104, lowerTwo_row_3105, lowerTwo_row_3106, lowerTwo_row_3107, lowerTwo_row_3108, lowerTwo_row_3109, lowerTwo_row_3110, lowerTwo_row_3111, lowerTwo_row_3112, lowerTwo_row_3113, lowerTwo_row_3114, lowerTwo_row_3115, lowerTwo_row_3116, lowerTwo_row_3117, lowerTwo_row_3118, lowerTwo_row_3119, lowerTwo_row_3120, lowerTwo_row_3121, lowerTwo_row_3122, lowerTwo_row_3123, lowerTwo_row_3124, lowerTwo_row_3125, lowerTwo_row_3126, lowerTwo_row_3127, lowerTwo_row_3128, lowerTwo_row_3129, lowerTwo_row_3130, lowerTwo_row_3131, lowerTwo_row_3132, lowerTwo_row_3133, lowerTwo_row_3134,
    lowerTwo_row_3135, lowerTwo_row_3136, lowerTwo_row_3137, lowerTwo_row_3138, lowerTwo_row_3139, lowerTwo_row_3140, lowerTwo_row_3141, lowerTwo_row_3142, lowerTwo_row_3143, lowerTwo_row_3144, lowerTwo_row_3145, lowerTwo_row_3146, lowerTwo_row_3147, lowerTwo_row_3148, lowerTwo_row_3149, lowerTwo_row_3150, lowerTwo_row_3151, lowerTwo_row_3152, lowerTwo_row_3153, lowerTwo_row_3154, lowerTwo_row_3155, lowerTwo_row_3156, lowerTwo_row_3157, lowerTwo_row_3158, lowerTwo_row_3159, lowerTwo_row_3160, lowerTwo_row_3161, lowerTwo_row_3162, lowerTwo_row_3163, lowerTwo_row_3164, lowerTwo_row_3165, lowerTwo_row_3166,
    lowerTwo_row_3167, lowerTwo_row_3168, lowerTwo_row_3169, lowerTwo_row_3170, lowerTwo_row_3171, lowerTwo_row_3172, lowerTwo_row_3173, lowerTwo_row_3174, lowerTwo_row_3175, lowerTwo_row_3176, lowerTwo_row_3177, lowerTwo_row_3178, lowerTwo_row_3179, lowerTwo_row_3180, lowerTwo_row_3181, lowerTwo_row_3182, lowerTwo_row_3183, lowerTwo_row_3184, lowerTwo_row_3185, lowerTwo_row_3186, lowerTwo_row_3187, lowerTwo_row_3188, lowerTwo_row_3189, lowerTwo_row_3190, lowerTwo_row_3191, lowerTwo_row_3192, lowerTwo_row_3193, lowerTwo_row_3194, lowerTwo_row_3195, lowerTwo_row_3196, lowerTwo_row_3197, lowerTwo_row_3198,
    lowerTwo_row_3199, lowerTwo_row_3200, lowerTwo_row_3201, lowerTwo_row_3202, lowerTwo_row_3203, lowerTwo_row_3204, lowerTwo_row_3205, lowerTwo_row_3206, lowerTwo_row_3207, lowerTwo_row_3208, lowerTwo_row_3209, lowerTwo_row_3210, lowerTwo_row_3211, lowerTwo_row_3212, lowerTwo_row_3213, lowerTwo_row_3214, lowerTwo_row_3215, lowerTwo_row_3216, lowerTwo_row_3217, lowerTwo_row_3218, lowerTwo_row_3219, lowerTwo_row_3220, lowerTwo_row_3221, lowerTwo_row_3222, lowerTwo_row_3223, lowerTwo_row_3224, lowerTwo_row_3225, lowerTwo_row_3226, lowerTwo_row_3227, lowerTwo_row_3228, lowerTwo_row_3229, lowerTwo_row_3230,
    lowerTwo_row_3231, lowerTwo_row_3232, lowerTwo_row_3233, lowerTwo_row_3234, lowerTwo_row_3235, lowerTwo_row_3236, lowerTwo_row_3237, lowerTwo_row_3238, lowerTwo_row_3239, lowerTwo_row_3240, lowerTwo_row_3241, lowerTwo_row_3242, lowerTwo_row_3243, lowerTwo_row_3244, lowerTwo_row_3245, lowerTwo_row_3246, lowerTwo_row_3247, lowerTwo_row_3248, lowerTwo_row_3249, lowerTwo_row_3250, lowerTwo_row_3251, lowerTwo_row_3252, lowerTwo_row_3253, lowerTwo_row_3254, lowerTwo_row_3255, lowerTwo_row_3256, lowerTwo_row_3257, lowerTwo_row_3258, lowerTwo_row_3259, lowerTwo_row_3260, lowerTwo_row_3261, lowerTwo_row_3262,
    lowerTwo_row_3263, lowerTwo_row_3264, lowerTwo_row_3265, lowerTwo_row_3266, lowerTwo_row_3267, lowerTwo_row_3268, lowerTwo_row_3269, lowerTwo_row_3270, lowerTwo_row_3271, lowerTwo_row_3272, lowerTwo_row_3273, lowerTwo_row_3274, lowerTwo_row_3275, lowerTwo_row_3276, lowerTwo_row_3277, lowerTwo_row_3278, lowerTwo_row_3279, lowerTwo_row_3280, lowerTwo_row_3281, lowerTwo_row_3282, lowerTwo_row_3283, lowerTwo_row_3284, lowerTwo_row_3285, lowerTwo_row_3286, lowerTwo_row_3287, lowerTwo_row_3288, lowerTwo_row_3289, lowerTwo_row_3290, lowerTwo_row_3291, lowerTwo_row_3292, lowerTwo_row_3293, lowerTwo_row_3294,
    lowerTwo_row_3295, lowerTwo_row_3296, lowerTwo_row_3297, lowerTwo_row_3298, lowerTwo_row_3299, lowerTwo_row_3300, lowerTwo_row_3301, lowerTwo_row_3302, lowerTwo_row_3303, lowerTwo_row_3304, lowerTwo_row_3305, lowerTwo_row_3306, lowerTwo_row_3307, lowerTwo_row_3308, lowerTwo_row_3309, lowerTwo_row_3310, lowerTwo_row_3311, lowerTwo_row_3312, lowerTwo_row_3313, lowerTwo_row_3314, lowerTwo_row_3315, lowerTwo_row_3316, lowerTwo_row_3317, lowerTwo_row_3318, lowerTwo_row_3319, lowerTwo_row_3320, lowerTwo_row_3321, lowerTwo_row_3322, lowerTwo_row_3323, lowerTwo_row_3324, lowerTwo_row_3325, lowerTwo_row_3326,
    lowerTwo_row_3327, lowerTwo_row_3328, lowerTwo_row_3329, lowerTwo_row_3330, lowerTwo_row_3331, lowerTwo_row_3332, lowerTwo_row_3333, lowerTwo_row_3334, lowerTwo_row_3335, lowerTwo_row_3336, lowerTwo_row_3337, lowerTwo_row_3338, lowerTwo_row_3339, lowerTwo_row_3340, lowerTwo_row_3341, lowerTwo_row_3342, lowerTwo_row_3343, lowerTwo_row_3344, lowerTwo_row_3345, lowerTwo_row_3346, lowerTwo_row_3347, lowerTwo_row_3348, lowerTwo_row_3349, lowerTwo_row_3350, lowerTwo_row_3351, lowerTwo_row_3352, lowerTwo_row_3353, lowerTwo_row_3354, lowerTwo_row_3355, lowerTwo_row_3356, lowerTwo_row_3357, lowerTwo_row_3358,
    lowerTwo_row_3359, lowerTwo_row_3360, lowerTwo_row_3361, lowerTwo_row_3362, lowerTwo_row_3363, lowerTwo_row_3364, lowerTwo_row_3365, lowerTwo_row_3366, lowerTwo_row_3367, lowerTwo_row_3368, lowerTwo_row_3369, lowerTwo_row_3370, lowerTwo_row_3371, lowerTwo_row_3372, lowerTwo_row_3373, lowerTwo_row_3374, lowerTwo_row_3375, lowerTwo_row_3376, lowerTwo_row_3377, lowerTwo_row_3378, lowerTwo_row_3379, lowerTwo_row_3380, lowerTwo_row_3381, lowerTwo_row_3382, lowerTwo_row_3383, lowerTwo_row_3384, lowerTwo_row_3385, lowerTwo_row_3386, lowerTwo_row_3387, lowerTwo_row_3388, lowerTwo_row_3389, lowerTwo_row_3390,
    lowerTwo_row_3391, lowerTwo_row_3392, lowerTwo_row_3393, lowerTwo_row_3394, lowerTwo_row_3395, lowerTwo_row_3396, lowerTwo_row_3397, lowerTwo_row_3398, lowerTwo_row_3399, lowerTwo_row_3400, lowerTwo_row_3401, lowerTwo_row_3402, lowerTwo_row_3403, lowerTwo_row_3404, lowerTwo_row_3405, lowerTwo_row_3406, lowerTwo_row_3407, lowerTwo_row_3408, lowerTwo_row_3409, lowerTwo_row_3410, lowerTwo_row_3411, lowerTwo_row_3412, lowerTwo_row_3413, lowerTwo_row_3414, lowerTwo_row_3415, lowerTwo_row_3416, lowerTwo_row_3417, lowerTwo_row_3418, lowerTwo_row_3419, lowerTwo_row_3420, lowerTwo_row_3421, lowerTwo_row_3422,
    lowerTwo_row_3423, lowerTwo_row_3424, lowerTwo_row_3425, lowerTwo_row_3426, lowerTwo_row_3427, lowerTwo_row_3428, lowerTwo_row_3429, lowerTwo_row_3430, lowerTwo_row_3431, lowerTwo_row_3432, lowerTwo_row_3433, lowerTwo_row_3434, lowerTwo_row_3435, lowerTwo_row_3436, lowerTwo_row_3437, lowerTwo_row_3438, lowerTwo_row_3439, lowerTwo_row_3440, lowerTwo_row_3441, lowerTwo_row_3442, lowerTwo_row_3443, lowerTwo_row_3444, lowerTwo_row_3445, lowerTwo_row_3446, lowerTwo_row_3447, lowerTwo_row_3448, lowerTwo_row_3449, lowerTwo_row_3450, lowerTwo_row_3451, lowerTwo_row_3452, lowerTwo_row_3453, lowerTwo_row_3454,
    lowerTwo_row_3455, lowerTwo_row_3456, lowerTwo_row_3457, lowerTwo_row_3458, lowerTwo_row_3459, lowerTwo_row_3460, lowerTwo_row_3461, lowerTwo_row_3462, lowerTwo_row_3463, lowerTwo_row_3464, lowerTwo_row_3465, lowerTwo_row_3466, lowerTwo_row_3467, lowerTwo_row_3468, lowerTwo_row_3469, lowerTwo_row_3470, lowerTwo_row_3471, lowerTwo_row_3472, lowerTwo_row_3473, lowerTwo_row_3474, lowerTwo_row_3475, lowerTwo_row_3476, lowerTwo_row_3477, lowerTwo_row_3478, lowerTwo_row_3479, lowerTwo_row_3480, lowerTwo_row_3481, lowerTwo_row_3482, lowerTwo_row_3483, lowerTwo_row_3484, lowerTwo_row_3485, lowerTwo_row_3486,
    lowerTwo_row_3487, lowerTwo_row_3488, lowerTwo_row_3489, lowerTwo_row_3490, lowerTwo_row_3491, lowerTwo_row_3492, lowerTwo_row_3493, lowerTwo_row_3494, lowerTwo_row_3495, lowerTwo_row_3496, lowerTwo_row_3497, lowerTwo_row_3498, lowerTwo_row_3499, lowerTwo_row_3500, lowerTwo_row_3501, lowerTwo_row_3502, lowerTwo_row_3503, lowerTwo_row_3504, lowerTwo_row_3505, lowerTwo_row_3506, lowerTwo_row_3507, lowerTwo_row_3508, lowerTwo_row_3509, lowerTwo_row_3510, lowerTwo_row_3511, lowerTwo_row_3512, lowerTwo_row_3513, lowerTwo_row_3514, lowerTwo_row_3515, lowerTwo_row_3516, lowerTwo_row_3517, lowerTwo_row_3518,
    lowerTwo_row_3519, lowerTwo_row_3520, lowerTwo_row_3521, lowerTwo_row_3522, lowerTwo_row_3523, lowerTwo_row_3524, lowerTwo_row_3525, lowerTwo_row_3526, lowerTwo_row_3527, lowerTwo_row_3528, lowerTwo_row_3529, lowerTwo_row_3530, lowerTwo_row_3531, lowerTwo_row_3532, lowerTwo_row_3533, lowerTwo_row_3534, lowerTwo_row_3535, lowerTwo_row_3536, lowerTwo_row_3537, lowerTwo_row_3538, lowerTwo_row_3539, lowerTwo_row_3540, lowerTwo_row_3541, lowerTwo_row_3542, lowerTwo_row_3543, lowerTwo_row_3544, lowerTwo_row_3545, lowerTwo_row_3546, lowerTwo_row_3547, lowerTwo_row_3548, lowerTwo_row_3549, lowerTwo_row_3550,
    lowerTwo_row_3551, lowerTwo_row_3552, lowerTwo_row_3553, lowerTwo_row_3554, lowerTwo_row_3555, lowerTwo_row_3556, lowerTwo_row_3557, lowerTwo_row_3558, lowerTwo_row_3559, lowerTwo_row_3560, lowerTwo_row_3561, lowerTwo_row_3562, lowerTwo_row_3563, lowerTwo_row_3564, lowerTwo_row_3565, lowerTwo_row_3566, lowerTwo_row_3567, lowerTwo_row_3568, lowerTwo_row_3569, lowerTwo_row_3570, lowerTwo_row_3571, lowerTwo_row_3572, lowerTwo_row_3573, lowerTwo_row_3574, lowerTwo_row_3575, lowerTwo_row_3576, lowerTwo_row_3577, lowerTwo_row_3578, lowerTwo_row_3579, lowerTwo_row_3580, lowerTwo_row_3581, lowerTwo_row_3582,
    lowerTwo_row_3583, lowerTwo_row_3584, lowerTwo_row_3585, lowerTwo_row_3586, lowerTwo_row_3587, lowerTwo_row_3588, lowerTwo_row_3589, lowerTwo_row_3590, lowerTwo_row_3591, lowerTwo_row_3592, lowerTwo_row_3593, lowerTwo_row_3594, lowerTwo_row_3595, lowerTwo_row_3596, lowerTwo_row_3597, lowerTwo_row_3598, lowerTwo_row_3599, lowerTwo_row_3600, lowerTwo_row_3601, lowerTwo_row_3602, lowerTwo_row_3603, lowerTwo_row_3604, lowerTwo_row_3605, lowerTwo_row_3606, lowerTwo_row_3607, lowerTwo_row_3608, lowerTwo_row_3609, lowerTwo_row_3610, lowerTwo_row_3611, lowerTwo_row_3612, lowerTwo_row_3613, lowerTwo_row_3614,
    lowerTwo_row_3615, lowerTwo_row_3616, lowerTwo_row_3617, lowerTwo_row_3618, lowerTwo_row_3619, lowerTwo_row_3620, lowerTwo_row_3621, lowerTwo_row_3622, lowerTwo_row_3623, lowerTwo_row_3624, lowerTwo_row_3625, lowerTwo_row_3626, lowerTwo_row_3627, lowerTwo_row_3628, lowerTwo_row_3629, lowerTwo_row_3630, lowerTwo_row_3631, lowerTwo_row_3632, lowerTwo_row_3633, lowerTwo_row_3634, lowerTwo_row_3635, lowerTwo_row_3636, lowerTwo_row_3637, lowerTwo_row_3638, lowerTwo_row_3639, lowerTwo_row_3640, lowerTwo_row_3641, lowerTwo_row_3642, lowerTwo_row_3643, lowerTwo_row_3644, lowerTwo_row_3645, lowerTwo_row_3646,
    lowerTwo_row_3647, lowerTwo_row_3648, lowerTwo_row_3649, lowerTwo_row_3650, lowerTwo_row_3651, lowerTwo_row_3652, lowerTwo_row_3653, lowerTwo_row_3654, lowerTwo_row_3655, lowerTwo_row_3656, lowerTwo_row_3657, lowerTwo_row_3658, lowerTwo_row_3659, lowerTwo_row_3660, lowerTwo_row_3661, lowerTwo_row_3662, lowerTwo_row_3663, lowerTwo_row_3664, lowerTwo_row_3665, lowerTwo_row_3666, lowerTwo_row_3667, lowerTwo_row_3668, lowerTwo_row_3669, lowerTwo_row_3670, lowerTwo_row_3671, lowerTwo_row_3672, lowerTwo_row_3673, lowerTwo_row_3674, lowerTwo_row_3675, lowerTwo_row_3676, lowerTwo_row_3677, lowerTwo_row_3678,
    lowerTwo_row_3679, lowerTwo_row_3680, lowerTwo_row_3681, lowerTwo_row_3682, lowerTwo_row_3683, lowerTwo_row_3684, lowerTwo_row_3685, lowerTwo_row_3686, lowerTwo_row_3687, lowerTwo_row_3688, lowerTwo_row_3689, lowerTwo_row_3690, lowerTwo_row_3691, lowerTwo_row_3692, lowerTwo_row_3693, lowerTwo_row_3694, lowerTwo_row_3695, lowerTwo_row_3696, lowerTwo_row_3697, lowerTwo_row_3698, lowerTwo_row_3699, lowerTwo_row_3700, lowerTwo_row_3701, lowerTwo_row_3702, lowerTwo_row_3703, lowerTwo_row_3704, lowerTwo_row_3705, lowerTwo_row_3706, lowerTwo_row_3707, lowerTwo_row_3708, lowerTwo_row_3709, lowerTwo_row_3710,
    lowerTwo_row_3711, lowerTwo_row_3712, lowerTwo_row_3713, lowerTwo_row_3714, lowerTwo_row_3715, lowerTwo_row_3716, lowerTwo_row_3717, lowerTwo_row_3718, lowerTwo_row_3719, lowerTwo_row_3720, lowerTwo_row_3721, lowerTwo_row_3722, lowerTwo_row_3723, lowerTwo_row_3724, lowerTwo_row_3725, lowerTwo_row_3726, lowerTwo_row_3727, lowerTwo_row_3728, lowerTwo_row_3729, lowerTwo_row_3730, lowerTwo_row_3731, lowerTwo_row_3732, lowerTwo_row_3733, lowerTwo_row_3734, lowerTwo_row_3735, lowerTwo_row_3736, lowerTwo_row_3737, lowerTwo_row_3738, lowerTwo_row_3739, lowerTwo_row_3740, lowerTwo_row_3741, lowerTwo_row_3742,
    lowerTwo_row_3743, lowerTwo_row_3744, lowerTwo_row_3745, lowerTwo_row_3746, lowerTwo_row_3747, lowerTwo_row_3748, lowerTwo_row_3749, lowerTwo_row_3750, lowerTwo_row_3751, lowerTwo_row_3752, lowerTwo_row_3753, lowerTwo_row_3754, lowerTwo_row_3755, lowerTwo_row_3756, lowerTwo_row_3757, lowerTwo_row_3758, lowerTwo_row_3759, lowerTwo_row_3760, lowerTwo_row_3761, lowerTwo_row_3762, lowerTwo_row_3763, lowerTwo_row_3764, lowerTwo_row_3765, lowerTwo_row_3766, lowerTwo_row_3767, lowerTwo_row_3768, lowerTwo_row_3769, lowerTwo_row_3770, lowerTwo_row_3771, lowerTwo_row_3772, lowerTwo_row_3773, lowerTwo_row_3774,
    lowerTwo_row_3775, lowerTwo_row_3776, lowerTwo_row_3777, lowerTwo_row_3778, lowerTwo_row_3779, lowerTwo_row_3780, lowerTwo_row_3781, lowerTwo_row_3782, lowerTwo_row_3783, lowerTwo_row_3784, lowerTwo_row_3785, lowerTwo_row_3786, lowerTwo_row_3787, lowerTwo_row_3788, lowerTwo_row_3789, lowerTwo_row_3790, lowerTwo_row_3791, lowerTwo_row_3792, lowerTwo_row_3793, lowerTwo_row_3794, lowerTwo_row_3795, lowerTwo_row_3796, lowerTwo_row_3797, lowerTwo_row_3798, lowerTwo_row_3799, lowerTwo_row_3800, lowerTwo_row_3801, lowerTwo_row_3802, lowerTwo_row_3803, lowerTwo_row_3804, lowerTwo_row_3805, lowerTwo_row_3806,
    lowerTwo_row_3807, lowerTwo_row_3808, lowerTwo_row_3809, lowerTwo_row_3810, lowerTwo_row_3811, lowerTwo_row_3812, lowerTwo_row_3813, lowerTwo_row_3814, lowerTwo_row_3815, lowerTwo_row_3816, lowerTwo_row_3817, lowerTwo_row_3818, lowerTwo_row_3819, lowerTwo_row_3820, lowerTwo_row_3821, lowerTwo_row_3822, lowerTwo_row_3823, lowerTwo_row_3824, lowerTwo_row_3825, lowerTwo_row_3826, lowerTwo_row_3827, lowerTwo_row_3828, lowerTwo_row_3829, lowerTwo_row_3830, lowerTwo_row_3831, lowerTwo_row_3832, lowerTwo_row_3833, lowerTwo_row_3834, lowerTwo_row_3835, lowerTwo_row_3836, lowerTwo_row_3837, lowerTwo_row_3838,
    lowerTwo_row_3839, lowerTwo_row_3840, lowerTwo_row_3841, lowerTwo_row_3842, lowerTwo_row_3843, lowerTwo_row_3844, lowerTwo_row_3845, lowerTwo_row_3846, lowerTwo_row_3847, lowerTwo_row_3848, lowerTwo_row_3849, lowerTwo_row_3850, lowerTwo_row_3851, lowerTwo_row_3852, lowerTwo_row_3853, lowerTwo_row_3854, lowerTwo_row_3855, lowerTwo_row_3856, lowerTwo_row_3857, lowerTwo_row_3858, lowerTwo_row_3859, lowerTwo_row_3860, lowerTwo_row_3861, lowerTwo_row_3862, lowerTwo_row_3863, lowerTwo_row_3864, lowerTwo_row_3865, lowerTwo_row_3866, lowerTwo_row_3867, lowerTwo_row_3868, lowerTwo_row_3869, lowerTwo_row_3870,
    lowerTwo_row_3871, lowerTwo_row_3872, lowerTwo_row_3873, lowerTwo_row_3874, lowerTwo_row_3875, lowerTwo_row_3876, lowerTwo_row_3877, lowerTwo_row_3878, lowerTwo_row_3879, lowerTwo_row_3880, lowerTwo_row_3881, lowerTwo_row_3882, lowerTwo_row_3883, lowerTwo_row_3884, lowerTwo_row_3885, lowerTwo_row_3886, lowerTwo_row_3887, lowerTwo_row_3888, lowerTwo_row_3889, lowerTwo_row_3890, lowerTwo_row_3891, lowerTwo_row_3892, lowerTwo_row_3893, lowerTwo_row_3894, lowerTwo_row_3895, lowerTwo_row_3896, lowerTwo_row_3897, lowerTwo_row_3898, lowerTwo_row_3899, lowerTwo_row_3900, lowerTwo_row_3901, lowerTwo_row_3902,
    lowerTwo_row_3903, lowerTwo_row_3904, lowerTwo_row_3905, lowerTwo_row_3906, lowerTwo_row_3907, lowerTwo_row_3908, lowerTwo_row_3909, lowerTwo_row_3910, lowerTwo_row_3911, lowerTwo_row_3912, lowerTwo_row_3913, lowerTwo_row_3914, lowerTwo_row_3915, lowerTwo_row_3916, lowerTwo_row_3917, lowerTwo_row_3918, lowerTwo_row_3919, lowerTwo_row_3920, lowerTwo_row_3921, lowerTwo_row_3922, lowerTwo_row_3923, lowerTwo_row_3924, lowerTwo_row_3925, lowerTwo_row_3926, lowerTwo_row_3927, lowerTwo_row_3928, lowerTwo_row_3929, lowerTwo_row_3930, lowerTwo_row_3931, lowerTwo_row_3932, lowerTwo_row_3933, lowerTwo_row_3934,
    lowerTwo_row_3935, lowerTwo_row_3936, lowerTwo_row_3937, lowerTwo_row_3938, lowerTwo_row_3939, lowerTwo_row_3940, lowerTwo_row_3941, lowerTwo_row_3942, lowerTwo_row_3943, lowerTwo_row_3944, lowerTwo_row_3945, lowerTwo_row_3946, lowerTwo_row_3947, lowerTwo_row_3948, lowerTwo_row_3949, lowerTwo_row_3950, lowerTwo_row_3951, lowerTwo_row_3952, lowerTwo_row_3953, lowerTwo_row_3954, lowerTwo_row_3955, lowerTwo_row_3956, lowerTwo_row_3957, lowerTwo_row_3958, lowerTwo_row_3959, lowerTwo_row_3960, lowerTwo_row_3961, lowerTwo_row_3962, lowerTwo_row_3963, lowerTwo_row_3964, lowerTwo_row_3965, lowerTwo_row_3966,
    lowerTwo_row_3967, lowerTwo_row_3968, lowerTwo_row_3969, lowerTwo_row_3970, lowerTwo_row_3971, lowerTwo_row_3972, lowerTwo_row_3973, lowerTwo_row_3974, lowerTwo_row_3975, lowerTwo_row_3976, lowerTwo_row_3977, lowerTwo_row_3978, lowerTwo_row_3979, lowerTwo_row_3980, lowerTwo_row_3981, lowerTwo_row_3982, lowerTwo_row_3983, lowerTwo_row_3984, lowerTwo_row_3985, lowerTwo_row_3986, lowerTwo_row_3987, lowerTwo_row_3988, lowerTwo_row_3989, lowerTwo_row_3990, lowerTwo_row_3991, lowerTwo_row_3992, lowerTwo_row_3993, lowerTwo_row_3994, lowerTwo_row_3995, lowerTwo_row_3996, lowerTwo_row_3997, lowerTwo_row_3998,
    lowerTwo_row_3999, lowerTwo_row_4000, lowerTwo_row_4001, lowerTwo_row_4002, lowerTwo_row_4003, lowerTwo_row_4004, lowerTwo_row_4005, lowerTwo_row_4006, lowerTwo_row_4007, lowerTwo_row_4008, lowerTwo_row_4009, lowerTwo_row_4010, lowerTwo_row_4011, lowerTwo_row_4012, lowerTwo_row_4013, lowerTwo_row_4014, lowerTwo_row_4015, lowerTwo_row_4016, lowerTwo_row_4017, lowerTwo_row_4018, lowerTwo_row_4019, lowerTwo_row_4020, lowerTwo_row_4021, lowerTwo_row_4022, lowerTwo_row_4023, lowerTwo_row_4024, lowerTwo_row_4025, lowerTwo_row_4026, lowerTwo_row_4027, lowerTwo_row_4028, lowerTwo_row_4029, lowerTwo_row_4030,
    lowerTwo_row_4031, lowerTwo_row_4032, lowerTwo_row_4033, lowerTwo_row_4034, lowerTwo_row_4035, lowerTwo_row_4036, lowerTwo_row_4037, lowerTwo_row_4038, lowerTwo_row_4039, lowerTwo_row_4040, lowerTwo_row_4041, lowerTwo_row_4042, lowerTwo_row_4043, lowerTwo_row_4044, lowerTwo_row_4045, lowerTwo_row_4046, lowerTwo_row_4047, lowerTwo_row_4048, lowerTwo_row_4049, lowerTwo_row_4050, lowerTwo_row_4051, lowerTwo_row_4052, lowerTwo_row_4053, lowerTwo_row_4054, lowerTwo_row_4055, lowerTwo_row_4056, lowerTwo_row_4057, lowerTwo_row_4058, lowerTwo_row_4059, lowerTwo_row_4060, lowerTwo_row_4061, lowerTwo_row_4062,
    lowerTwo_row_4063, lowerTwo_row_4064, lowerTwo_row_4065, lowerTwo_row_4066, lowerTwo_row_4067, lowerTwo_row_4068, lowerTwo_row_4069, lowerTwo_row_4070, lowerTwo_row_4071, lowerTwo_row_4072, lowerTwo_row_4073, lowerTwo_row_4074, lowerTwo_row_4075, lowerTwo_row_4076, lowerTwo_row_4077, lowerTwo_row_4078, lowerTwo_row_4079, lowerTwo_row_4080, lowerTwo_row_4081, lowerTwo_row_4082, lowerTwo_row_4083, lowerTwo_row_4084, lowerTwo_row_4085, lowerTwo_row_4086, lowerTwo_row_4087, lowerTwo_row_4088, lowerTwo_row_4089, lowerTwo_row_4090, lowerTwo_row_4091, lowerTwo_row_4092, lowerTwo_row_4093, lowerTwo_row_4094,
    lowerTwo_row_4095
    ]
  decide

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
