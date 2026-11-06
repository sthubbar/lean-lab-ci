import LeanLab.Halupczok2012.U1439Thm2Reduction

/-!
Halupczok journal pages 337 to 338, Lemma 2.2.
These full range estimates retain a harmless third power of the logarithm.
They reuse the lcm sum already proved in U1439Combin.
Mathlib search found Finset.sum_mul_sq_le_sq_mul_sq.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Progression398

open Finset
open scoped Classical

/-- The overlap count in Lemma 2.2 on page 338.
The residues can vary with the modulus.
The full range lcm bound costs a third power of the logarithm. -/
theorem residue_moment {W : Finset ℕ} {x y : ℝ} (hy : 0 ≤ y)
    (hW : ∀ m ∈ W, x < m ∧ (m : ℝ) ≤ x + y) (N : ℕ) (a : ℕ → ℤ) :
    ∑ m ∈ W, ((((Icc 1 N).filter (fun q : ℕ => (m : ℤ) ≡ a q [ZMOD q])).card : ℕ) : ℝ) ^ 2 ≤ y * (1 + Real.log N) ^ 3 + (N : ℝ) ^ 2 := by
  have hsq : ∀ m, ((((Icc 1 N).filter (fun q : ℕ => (m : ℤ) ≡ a q [ZMOD q])).card : ℕ) : ℝ) ^ 2 = ∑ q1 ∈ Icc 1 N, ∑ q2 ∈ Icc 1 N,
      (if (m : ℤ) ≡ a q1 [ZMOD q1] ∧ (m : ℤ) ≡ a q2 [ZMOD q2] then (1 : ℝ) else 0) := by
    intro m
    rw [Finset.card_filter, sq]
    push_cast
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro q1 _
    apply Finset.sum_congr rfl; intro q2 _
    by_cases h1 : (m : ℤ) ≡ a q1 [ZMOD q1] <;> by_cases h2 : (m : ℤ) ≡ a q2 [ZMOD q2] <;> simp [h1, h2]
  simp_rw [hsq]
  rw [Finset.sum_comm]
  have hrow : ∀ q1 ∈ Icc 1 N, ∀ q2 ∈ Icc 1 N, ∑ m ∈ W,
      (if (m : ℤ) ≡ a q1 [ZMOD q1] ∧ (m : ℤ) ≡ a q2 [ZMOD q2] then (1 : ℝ) else 0) ≤
      y * ((Nat.lcm q1 q2 : ℕ) : ℝ)⁻¹ + 1 := by
    intro q1 hq1 q2 hq2
    rw [Finset.mem_Icc] at hq1 hq2
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hl : 0 < Nat.lcm q1 q2 := Nat.lcm_pos (by omega) (by omega)
    have := card_cong_le (S := W.filter (fun m : ℕ => (m : ℤ) ≡ a q1 [ZMOD q1] ∧
      (m : ℤ) ≡ a q2 [ZMOD q2])) (x := x) (y := y) hl hy
      (fun m hm => hW m (Finset.mem_filter.mp hm).1)
      (fun m hm m' hm' => by
        obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hm
        obtain ⟨-, h1', h2'⟩ := Finset.mem_filter.mp hm'
        exact modEq_lcm (h1.trans h1'.symm) (h2.trans h2'.symm))
    rw [div_eq_mul_inv] at this
    exact this
  calc ∑ q1 ∈ Icc 1 N, ∑ m ∈ W, ∑ q2 ∈ Icc 1 N,
        (if (m : ℤ) ≡ a q1 [ZMOD q1] ∧ (m : ℤ) ≡ a q2 [ZMOD q2] then (1 : ℝ) else 0)
      = ∑ q1 ∈ Icc 1 N, ∑ q2 ∈ Icc 1 N, ∑ m ∈ W,
        (if (m : ℤ) ≡ a q1 [ZMOD q1] ∧ (m : ℤ) ≡ a q2 [ZMOD q2] then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl; intro q1 _; rw [Finset.sum_comm]
    _ ≤ ∑ q1 ∈ Icc 1 N, ∑ q2 ∈ Icc 1 N, (y * ((Nat.lcm q1 q2 : ℕ) : ℝ)⁻¹ + 1) :=
        Finset.sum_le_sum (fun q1 h1 => Finset.sum_le_sum (fun q2 h2 => hrow q1 h1 q2 h2))
    _ = y * ∑ q1 ∈ Icc 1 N, ∑ q2 ∈ Icc 1 N, ((Nat.lcm q1 q2 : ℕ) : ℝ)⁻¹ + (N : ℝ) ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
          mul_one, Finset.mul_sum]
        push_cast; ring
    _ ≤ y * (1 + Real.log N) ^ 3 + (N : ℝ) ^ 2 := by
        gcongr; exact sum_inv_lcm_le N


/-- Cauchy Schwarz for the progression filters on pages 336 to 338. -/
theorem residue_cauchy (W : Finset ℕ) (w : ℕ → ℝ) (N : ℕ) (a : ℕ → ℤ) :
    (∑ q ∈ Icc 1 N, |∑ m ∈ W.filter (fun m : ℕ => (m : ℤ) ≡ a q [ZMOD q]), w m|) ^ 2 ≤
      (∑ m ∈ W, w m ^ 2) * ∑ m ∈ W, ((((Icc 1 N).filter (fun q : ℕ => (m : ℤ) ≡ a q [ZMOD q])).card : ℕ) : ℝ) ^ 2 := by
  have h1 : ∑ q ∈ Icc 1 N, |∑ m ∈ W.filter (fun m : ℕ => (m : ℤ) ≡ a q [ZMOD q]), w m| ≤
      ∑ m ∈ W, |w m| * ((((Icc 1 N).filter (fun q : ℕ => (m : ℤ) ≡ a q [ZMOD q])).card : ℕ) : ℝ) := by
    calc ∑ q ∈ Icc 1 N, |∑ m ∈ W.filter (fun m : ℕ => (m : ℤ) ≡ a q [ZMOD q]), w m|
        ≤ ∑ q ∈ Icc 1 N, ∑ m ∈ W, (if (m : ℤ) ≡ a q [ZMOD q] then |w m| else 0) := by
          apply Finset.sum_le_sum; intro q _
          rw [← Finset.sum_filter]
          exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ m ∈ W, |w m| * ((((Icc 1 N).filter (fun q : ℕ => (m : ℤ) ≡ a q [ZMOD q])).card : ℕ) : ℝ) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro m _
          rw [Finset.card_filter]; push_cast
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro q _
          split_ifs <;> simp
  have h0 : 0 ≤ ∑ q ∈ Icc 1 N, |∑ m ∈ W.filter (fun m : ℕ => (m : ℤ) ≡ a q [ZMOD q]), w m| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  calc _ ≤ (∑ m ∈ W, |w m| * ((((Icc 1 N).filter (fun q : ℕ => (m : ℤ) ≡ a q [ZMOD q])).card : ℕ) : ℝ)) ^ 2 := by gcongr
    _ ≤ (∑ m ∈ W, |w m| ^ 2) * ∑ m ∈ W, ((((Icc 1 N).filter (fun q : ℕ => (m : ℤ) ≡ a q [ZMOD q])).card : ℕ) : ℝ) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ m ∈ W, w m ^ 2) * ∑ m ∈ W, ((((Icc 1 N).filter (fun q : ℕ => (m : ℤ) ≡ a q [ZMOD q])).card : ℕ) : ℝ) ^ 2 := by simp_rw [sq_abs]


/-- The full range version of Lemma 2.2 on page 338.
This weaker logarithm suffices for every logarithmic saving in Theorem 7. -/
theorem residue_large_sieve {W : Finset ℕ} {x y : ℝ} (hy : 0 ≤ y)
    (hW : ∀ m ∈ W, x < m ∧ (m : ℝ) ≤ x + y)
    (w : ℕ → ℝ) (N : ℕ) (a : ℕ → ℤ) :
    (∑ q ∈ Icc 1 N, |∑ m ∈ W.filter (fun m : ℕ => (m : ℤ) ≡ a q [ZMOD q]), w m|) ^ 2 ≤
      (∑ m ∈ W, w m ^ 2) * (y * (1 + Real.log N) ^ 3 + (N : ℝ) ^ 2) :=
  (residue_cauchy W w N a).trans
    (mul_le_mul_of_nonneg_left (residue_moment hy hW N a)
      (sum_nonneg fun _ _ => sq_nonneg _))

/-- The even arguments in display 4.1 on page 343 occupy a window of length 2R. -/
theorem even_large_sieve (X R : ℝ) (hR : 0 ≤ R)
    (w : ℕ → ℝ) (N : ℕ) (a : ℕ → ℕ) :
    (∑ q ∈ Icc 1 N,
      |∑ k ∈ (kRange X R).filter (fun k => 2 * k ≡ a q [MOD q]), w k|) ^ 2 ≤
    (∑ k ∈ kRange X R, w k ^ 2) * (2 * R * (1 + Real.log N) ^ 3 + (N : ℝ) ^ 2) := by
  let W := (kRange X R).image (fun k => 2 * k)
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := by
    intro k j h
    dsimp only at h
    omega
  have hW : ∀ m ∈ W, 2 * X < (m : ℝ) ∧ (m : ℝ) ≤ 2 * X + 2 * R := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hm
    obtain ⟨_, h1, h2⟩ := mem_filter.mp hk
    push_cast
    constructor <;> linarith
  have h := residue_large_sieve (by positivity : 0 ≤ 2 * R) hW
    (fun m => w (m / 2)) N (fun q : ℕ => (a q : ℤ))
  have he : (∑ m ∈ W, w (m / 2) ^ 2) = ∑ k ∈ kRange X R, w k ^ 2 := by
    rw [show W = (kRange X R).image (fun k => 2 * k) from rfl, sum_image]
    · simp
    · exact fun _ _ _ _ h => hinj h
  have hs : ∀ q : ℕ, (∑ m ∈ W.filter (fun m : ℕ => (m : ℤ) ≡ (a q : ℤ) [ZMOD q]), w (m / 2)) =
      ∑ k ∈ (kRange X R).filter (fun k => 2 * k ≡ a q [MOD q]), w k := by
    intro q
    dsimp [W]
    rw [filter_image, sum_image]
    · simp only [Int.natCast_modEq_iff, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    · exact fun _ _ _ _ h => hinj h
  simpa only [he, hs] using h

/-- Cauchy Schwarz at the even arguments of display 4.1 on page 343. -/
theorem even_cauchy (W : Finset ℕ) (w : ℕ → ℝ) (N : ℕ) (a : ℕ → ℕ) :
    (∑ q ∈ Icc 1 N, |∑ m ∈ W.filter (fun m : ℕ => 2 * m ≡ a q [MOD q]), w m|) ^ 2 ≤
      (∑ m ∈ W, w m ^ 2) * ∑ m ∈ W, ((((Icc 1 N).filter (fun q : ℕ => 2 * m ≡ a q [MOD q])).card : ℕ) : ℝ) ^ 2 := by
  have h1 : ∑ q ∈ Icc 1 N, |∑ m ∈ W.filter (fun m : ℕ => 2 * m ≡ a q [MOD q]), w m| ≤
      ∑ m ∈ W, |w m| * ((((Icc 1 N).filter (fun q : ℕ => 2 * m ≡ a q [MOD q])).card : ℕ) : ℝ) := by
    calc ∑ q ∈ Icc 1 N, |∑ m ∈ W.filter (fun m : ℕ => 2 * m ≡ a q [MOD q]), w m|
        ≤ ∑ q ∈ Icc 1 N, ∑ m ∈ W, (if 2 * m ≡ a q [MOD q] then |w m| else 0) := by
          apply Finset.sum_le_sum; intro q _
          rw [← Finset.sum_filter]
          exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ m ∈ W, |w m| * ((((Icc 1 N).filter (fun q : ℕ => 2 * m ≡ a q [MOD q])).card : ℕ) : ℝ) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro m _
          rw [Finset.card_filter]; push_cast
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro q _
          split_ifs <;> simp
  have h0 : 0 ≤ ∑ q ∈ Icc 1 N, |∑ m ∈ W.filter (fun m : ℕ => 2 * m ≡ a q [MOD q]), w m| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  calc _ ≤ (∑ m ∈ W, |w m| * ((((Icc 1 N).filter (fun q : ℕ => 2 * m ≡ a q [MOD q])).card : ℕ) : ℝ)) ^ 2 := by gcongr
    _ ≤ (∑ m ∈ W, |w m| ^ 2) * ∑ m ∈ W, ((((Icc 1 N).filter (fun q : ℕ => 2 * m ≡ a q [MOD q])).card : ℕ) : ℝ) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ m ∈ W, w m ^ 2) * ∑ m ∈ W, ((((Icc 1 N).filter (fun q : ℕ => 2 * m ≡ a q [MOD q])).card : ℕ) : ℝ) ^ 2 := by simp_rw [sq_abs]



/-- Integer residue form of the even progression Cauchy Schwarz estimate. -/
theorem even_cauchy_int (W : Finset ℕ) (w : ℕ → ℝ) (N : ℕ) (a : ℕ → ℤ) :
    (∑ q ∈ Icc 1 N, |∑ m ∈ W.filter (fun m : ℕ => ((2 * m : ℕ) : ℤ) ≡ a q [ZMOD q]), w m|) ^ 2 ≤
      (∑ m ∈ W, w m ^ 2) * ∑ m ∈ W, ((((Icc 1 N).filter (fun q : ℕ => ((2 * m : ℕ) : ℤ) ≡ a q [ZMOD q])).card : ℕ) : ℝ) ^ 2 := by
  have h1 : ∑ q ∈ Icc 1 N, |∑ m ∈ W.filter (fun m : ℕ => ((2 * m : ℕ) : ℤ) ≡ a q [ZMOD q]), w m| ≤
      ∑ m ∈ W, |w m| * ((((Icc 1 N).filter (fun q : ℕ => ((2 * m : ℕ) : ℤ) ≡ a q [ZMOD q])).card : ℕ) : ℝ) := by
    calc ∑ q ∈ Icc 1 N, |∑ m ∈ W.filter (fun m : ℕ => ((2 * m : ℕ) : ℤ) ≡ a q [ZMOD q]), w m|
        ≤ ∑ q ∈ Icc 1 N, ∑ m ∈ W, (if ((2 * m : ℕ) : ℤ) ≡ a q [ZMOD q] then |w m| else 0) := by
          apply Finset.sum_le_sum; intro q _
          rw [← Finset.sum_filter]
          exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ m ∈ W, |w m| * ((((Icc 1 N).filter (fun q : ℕ => ((2 * m : ℕ) : ℤ) ≡ a q [ZMOD q])).card : ℕ) : ℝ) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro m _
          rw [Finset.card_filter]; push_cast
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro q _
          split_ifs <;> simp
  have h0 : 0 ≤ ∑ q ∈ Icc 1 N, |∑ m ∈ W.filter (fun m : ℕ => ((2 * m : ℕ) : ℤ) ≡ a q [ZMOD q]), w m| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  calc _ ≤ (∑ m ∈ W, |w m| * ((((Icc 1 N).filter (fun q : ℕ => ((2 * m : ℕ) : ℤ) ≡ a q [ZMOD q])).card : ℕ) : ℝ)) ^ 2 := by gcongr
    _ ≤ (∑ m ∈ W, |w m| ^ 2) * ∑ m ∈ W, ((((Icc 1 N).filter (fun q : ℕ => ((2 * m : ℕ) : ℤ) ≡ a q [ZMOD q])).card : ℕ) : ℝ) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ m ∈ W, w m ^ 2) * ∑ m ∈ W, ((((Icc 1 N).filter (fun q : ℕ => ((2 * m : ℕ) : ℤ) ≡ a q [ZMOD q])).card : ℕ) : ℝ) ^ 2 := by simp_rw [sq_abs]




end LeanLab.Halupczok2012.Progression398
