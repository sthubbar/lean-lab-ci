import LeanLab.Estermann1938.Parseval112
import LeanLab.Estermann1938.Coeff112
import LeanLab.Estermann1938.Decomp112b
import LeanLab.PNTPort.Vinogradov.SingSeries
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
Estermann 1938, P0091, page 311, displays 37 and 38.
The reduced residues are represented by zero through q minus one.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Estermann1938.Ramanujan112
open scoped BigOperators ArithmeticFunction.Moebius
open Decomp112 Parseval112 Coeff112 ComplexConjugate

/-- The reduced residue system in display 3, page 308. -/
def residues (q : ℕ) : Finset ℕ := (Finset.range q).filter (fun r => Nat.Coprime r q)

/-- The Ramanujan sum in display 3, with natural frequency m. -/
noncomputable def c (q m : ℕ) : ℂ := ∑ r ∈ residues q, phase ((r : ℝ) / q) m

/-- Landau's formula used on page 311, supplied here by the lab's proved Möbius inversion. -/
theorem c_eq_ramanujan {q : ℕ} (hq : 1 ≤ q) (m : ℕ) :
    c q m = (LeanLab.HeathBrown1985.ramanujan q m : ℂ) := by
  have h := LeanLab.PNTPort.Vinogradov.ramanujan_sum hq m
  convert h using 1
  unfold c residues
  apply Finset.sum_congr rfl
  intro r hr
  unfold phase LeanLab.PNTPort.LargeSieve.e
  congr 1
  push_cast
  ring

/-- Page 311: taking absolute values in the Möbius formula leaves a divisor sum. -/
theorem c_norm_le_divisor_sum {q : ℕ} (hq : 1 ≤ q) (m : ℕ) :
    ‖c q m‖ ≤ ∑ d ∈ (Nat.gcd m q).divisors, (d : ℝ) := by
  rw [c_eq_ramanujan hq, Complex.norm_real, LeanLab.HeathBrown1985.ramanujan]
  calc
    ‖∑ d ∈ (Nat.gcd m q).divisors, (d : ℝ) * (ArithmeticFunction.moebius (q / d) : ℝ)‖
        ≤ ∑ d ∈ (Nat.gcd m q).divisors,
          ‖(d : ℝ) * (ArithmeticFunction.moebius (q / d) : ℝ)‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_eq_abs]
      have hmu : |(ArithmeticFunction.moebius (q / d) : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q / d))
      simpa using mul_le_mul_of_nonneg_left hmu (Nat.cast_nonneg d : (0 : ℝ) ≤ d)

/-- Page 311: the sum of the divisors of g equals g times their reciprocal sum. -/
theorem divisor_sum_reciprocal (g : ℕ) :
    (∑ d ∈ g.divisors, (d : ℝ)) = (g : ℝ) * ∑ d ∈ g.divisors, (d : ℝ)⁻¹ := by
  classical
  rw [← Nat.sum_div_divisors g (fun d => (d : ℝ)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd)
    (by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne')]
  exact div_eq_mul_inv _ _

/-- Page 311: the reciprocal divisor sum is bounded by the harmonic sum up to q. -/
theorem reciprocal_divisors_le_log {g q : ℕ} (hg : 0 < g) (hgq : g ≤ q) :
    (∑ d ∈ g.divisors, (d : ℝ)⁻¹) ≤ 1 + Real.log q := by
  have hs : g.divisors ⊆ Finset.Icc 1 q := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
      (Nat.le_of_dvd hg (Nat.dvd_of_mem_divisors hd)).trans hgq⟩
  calc
    (∑ d ∈ g.divisors, (d : ℝ)⁻¹) ≤ ∑ d ∈ Finset.Icc 1 q, (d : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun d hd hnot => by positivity)
    _ = (harmonic q : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rfl
    _ ≤ _ := harmonic_le_one_add_log q

/-- Page 311, after display 37: the printed logarithmic Ramanujan bound. -/
theorem c_norm_le_gcd_log {q : ℕ} (hq : 1 ≤ q) (m : ℕ) :
    ‖c q m‖ ≤ (Nat.gcd q m : ℝ) * (1 + Real.log q) := by
  have hg : 0 < Nat.gcd m q := Nat.gcd_pos_of_pos_right m hq
  calc
    ‖c q m‖ ≤ ∑ d ∈ (Nat.gcd m q).divisors, (d : ℝ) := c_norm_le_divisor_sum hq m
    _ = (Nat.gcd m q : ℝ) * ∑ d ∈ (Nat.gcd m q).divisors, (d : ℝ)⁻¹ :=
      divisor_sum_reciprocal _
    _ ≤ (Nat.gcd m q : ℝ) * (1 + Real.log q) :=
      mul_le_mul_of_nonneg_left (reciprocal_divisors_le_log hg (Nat.gcd_le_right m (by omega)))
        (Nat.cast_nonneg _)
    _ = _ := by rw [Nat.gcd_comm]

/-- The shifted sum g2 in display 6, page 308. -/
noncomputable def g2 (n : ℕ) (x : ℝ) (q : ℕ) : ℂ :=
  ∑ r ∈ residues q, g1 n (x - (r : ℝ) / q) ^ 2

/-- Addition in the real argument multiplies phases, used between displays 32 and 37. -/
theorem phase_add_real (x y : ℝ) (m : ℕ) :
    phase (x + y) m = phase x m * phase y m := by
  unfold phase
  rw [Complex.ofReal_add, mul_add, add_mul, Complex.exp_add]

/-- Negating the real argument conjugates the phase, used before display 37. -/
theorem phase_neg (x : ℝ) (m : ℕ) :
    phase (-x) m = conj (phase x m) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, map_natCast, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

/-- The Ramanujan sum is real, giving the frequency sign symmetry used before display 37. -/
theorem c_conj {q : ℕ} (hq : 1 ≤ q) (m : ℕ) : conj (c q m) = c q m := by
  rw [c_eq_ramanujan hq]
  exact Complex.conj_ofReal _

/-- The negative frequency residue sum equals c, as used before display 37. -/
theorem negative_c {q : ℕ} (hq : 1 ≤ q) (m : ℕ) :
    (∑ r ∈ residues q, phase (-((r : ℝ) / q)) m) = c q m := by
  rw [← c_conj hq m]
  unfold c
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  exact phase_neg _ _

/-- Display 37, page 311, for the shifted sum defined in display 6. -/
theorem display37 (n : ℕ) (x : ℝ) {q : ℕ} (hq : 1 ≤ q) :
    g2 n x q = ∑ m ∈ Finset.Icc 1 (2 * n), (b n m : ℂ) * c q m * phase x m := by
  unfold g2
  simp_rw [fourierSquare n]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  calc
    (∑ r ∈ residues q, (b n m : ℂ) * phase (x - (r : ℝ) / q) m) =
        (b n m : ℂ) * phase x m * ∑ r ∈ residues q, phase (-((r : ℝ) / q)) m := by
      simp only [sub_eq_add_neg, phase_add_real, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = _ := by rw [negative_c hq]; ring

/-- Display 38, page 311: the bound on g2 from the coefficient and Ramanujan bounds. -/
theorem display38 (n : ℕ) (x : ℝ) {q : ℕ} (hq : 1 ≤ q) :
    ‖g2 n x q‖ ≤ 2 * (n : ℝ) * (1 + Real.log q) *
      ∑ m ∈ Finset.Icc 1 (2 * n), (Nat.gcd q m : ℝ) := by
  rw [display37 n x hq]
  calc
    ‖∑ m ∈ Finset.Icc 1 (2 * n), (b n m : ℂ) * c q m * phase x m‖ ≤
        ∑ m ∈ Finset.Icc 1 (2 * n), ‖(b n m : ℂ) * c q m * phase x m‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 (2 * n),
        2 * (n : ℝ) * (1 + Real.log q) * (Nat.gcd q m : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul, phase_norm, mul_one, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (b_nonneg n m)]
      have h := mul_le_mul (b_upper n m) (c_norm_le_gcd_log hq m)
        (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * n)
      convert h using 1 <;> ring
    _ = _ := by rw [Finset.mul_sum]

/-- Above modulus one, the two reduced residue endpoint conventions agree exactly. -/
theorem residues_eq_paper {q : ℕ} (hq : 2 ≤ q) :
    residues q = (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q) := by
  ext r
  simp only [residues, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨hr, hc⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp only [Nat.coprime_zero_left] at hc
      omega
    exact ⟨⟨by omega, by omega⟩, hc⟩
  · rintro ⟨⟨hr, hrq⟩, hc⟩
    have hne : r ≠ q := by
      rintro rfl
      simp only [Nat.coprime_self] at hc
      omega
    exact ⟨by omega, hc⟩

/-- The shifted sum g2 equals display 6 with the paper's exact endpoints. -/
theorem g2_eq_paper (n : ℕ) (x : ℝ) {q : ℕ} (hq : 1 ≤ q) :
    g2 n x q = ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
      g1 n (x - (r : ℝ) / q) ^ 2 := by
  by_cases hq1 : q = 1
  · subst q
    have hp := g1_periodic n (x - 1)
    have he : x - 1 + 1 = x := by ring
    rw [he] at hp
    simpa [g2, residues] using congrArg (fun z : ℂ => z ^ 2) hp
  · unfold g2
    rw [residues_eq_paper (by omega : 2 ≤ q)]

/-- The Ramanujan sum also equals display 3 with the paper's exact endpoints. -/
theorem c_eq_paper {q : ℕ} (hq : 1 ≤ q) (m : ℕ) :
    c q m = ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q), phase ((r : ℝ) / q) m := by
  by_cases hq1 : q = 1
  · subst q
    have hp := phase_period 0 m
    simpa [c, residues, phase] using hp.symm
  · unfold c
    rw [residues_eq_paper (by omega : 2 ≤ q)]

/-- The first bound in display 39 before dividing by the totient squared. -/
theorem g2_divisor_bound (n : ℕ) (x : ℝ) {q : ℕ} (hq : 1 ≤ q) :
    ‖g2 n x q‖ ≤ 4 * (n : ℝ) ^ 2 * (1 + Real.log q) * q.divisors.card := by
  have hs : (∑ m ∈ Finset.Icc 1 (2 * n), (Nat.gcd q m : ℝ)) ≤
      2 * (n : ℝ) * q.divisors.card := by
    exact_mod_cast Decomp112b.gcdSumBound q n hq
  have hC : 0 ≤ 2 * (n : ℝ) * (1 + Real.log q) := by
    have := Real.log_natCast_nonneg q
    positivity
  calc
    ‖g2 n x q‖ ≤ 2 * (n : ℝ) * (1 + Real.log q) *
      ∑ m ∈ Finset.Icc 1 (2 * n), (Nat.gcd q m : ℝ) := display38 n x hq
    _ ≤ (2 * (n : ℝ) * (1 + Real.log q)) * (2 * (n : ℝ) * q.divisors.card) :=
      mul_le_mul_of_nonneg_left hs hC
    _ = _ := by ring

/-- Display 39, page 312, first inequality with its totient normalization. -/
theorem display39_first (n : ℕ) (x : ℝ) {q : ℕ} (hq : 1 ≤ q) :
    ‖g2 n x q / (q.totient : ℂ) ^ 2‖ ≤
      4 * (n : ℝ) ^ 2 * (1 + Real.log q) * q.divisors.card / (q.totient : ℝ) ^ 2 := by
  rw [norm_div, norm_pow, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (g2_divisor_bound n x hq) (sq_nonneg _)

#print axioms residues_eq_paper
#print axioms g2_eq_paper
#print axioms c_eq_paper
#print axioms g2_divisor_bound
#print axioms display39_first

#print axioms phase_add_real
#print axioms phase_neg
#print axioms c_conj
#print axioms negative_c
#print axioms display37
#print axioms display38

#print axioms c_eq_ramanujan
#print axioms c_norm_le_divisor_sum
#print axioms divisor_sum_reciprocal
#print axioms reciprocal_divisors_le_log
#print axioms c_norm_le_gcd_log

end LeanLab.Estermann1938.Ramanujan112
