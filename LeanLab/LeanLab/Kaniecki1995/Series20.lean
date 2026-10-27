/-
P0022, page 369, absolute convergence and equation 20.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Kaniecki1995.PrimePowers95

namespace LeanLab.Kaniecki1995.Series20
open Real Complex
open scoped ArithmeticFunction.vonMangoldt LSeries.notation

/-- The prime power term in g on page 369, with exponent starting at two. -/
noncomputable def powerTerm (s : ℂ) (p : Nat.Primes) (k : ℕ) : ℂ :=
  (Real.log p : ℂ) / (p : ℂ) ^ (((k + 2 : ℕ) : ℂ) * s)

/-- The double sum defining g on page 369, in the printed order. -/
noncomputable def gSeries (s : ℂ) : ℂ := ∑' k : ℕ, ∑' p : Nat.Primes, powerTerm s p k

/-- Page 369. A geometric majorant for the prime power double series is summable. -/
theorem summable_majorant {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun pk : Nat.Primes × ℕ =>
      (pk.1 : ℝ) ^ (-σ - 1 / 2) * ((pk.1 : ℝ) ^ (-σ)) ^ pk.2) := by
  have hσ0 : 0 < σ := by linarith
  have htwo : (2 : ℝ) ^ (-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : 0 < 1 - (2 : ℝ) ^ (-σ) := by linarith
  have hp0 (p : Nat.Primes) : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hpq (p : Nat.Primes) : (p : ℝ) ^ (-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)
  apply (summable_prod_of_nonneg (fun _ => by positivity)).mpr
  constructor
  · intro p
    dsimp only
    exact (summable_geometric_of_lt_one (Real.rpow_nonneg (hp0 p).le _) (hpq p)).mul_left _
  · have hs : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-σ - 1 / 2)) :=
      Nat.Primes.summable_rpow.mpr (by linarith)
    apply (hs.mul_left (1 / (1 - (2 : ℝ) ^ (-σ)))).of_nonneg_of_le
    · intro p
      apply tsum_nonneg
      intro k
      positivity
    · intro p
      dsimp only
      rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.rpow_nonneg (hp0 p).le _) (hpq p)]
      have hq : (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast p.prop.two_le) (by linarith)
      have hi : (1 - (p : ℝ) ^ (-σ))⁻¹ ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hden
          (show 1 - (2 : ℝ) ^ (-σ) ≤ 1 - (p : ℝ) ^ (-σ) by linarith)
      simpa [one_div, mul_comm] using
        mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg (hp0 p).le (-σ - 1 / 2))

/-- Page 369. The norm of a prime power term is bounded by the summable majorant. -/
theorem norm_powerTerm_le {s : ℂ} (hs : 1 / 2 < s.re) (p : Nat.Primes) (k : ℕ) :
    ‖powerTerm s p k‖ ≤ (s.re - 1 / 2)⁻¹ *
      ((p : ℝ) ^ (-s.re - 1 / 2) * ((p : ℝ) ^ (-s.re)) ^ k) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have he : 0 < s.re - 1 / 2 := by linarith
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)
  have hlog := Real.log_le_rpow_div hp.le he
  have hn : ‖powerTerm s p k‖ = Real.log p * (p : ℝ) ^ (-((k + 2) * s.re)) := by
    unfold powerTerm
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hl, norm_natCast_cpow_of_pos p.prop.pos]
    simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
    rw [div_eq_mul_inv, ← Real.rpow_neg hp.le]
    push_cast
    rfl
  rw [hn]
  calc Real.log p * (p : ℝ) ^ (-((k + 2) * s.re)) ≤
      ((p : ℝ) ^ (s.re - 1 / 2) / (s.re - 1 / 2)) *
        (p : ℝ) ^ (-((k + 2) * s.re)) := by gcongr
    _ = (s.re - 1 / 2)⁻¹ *
        ((p : ℝ) ^ (-s.re - 1 / 2) * ((p : ℝ) ^ (-s.re)) ^ k) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le,
        div_eq_mul_inv, mul_assoc, ← Real.rpow_add hp]
      rw [← mul_assoc, mul_comm ((p : ℝ) ^ _) ((s.re - 1 / 2)⁻¹), mul_assoc,
        ← Real.rpow_add hp]
      congr 2
      ring

/-- Page 369. The double series defining g converges absolutely for Re s greater than one half. -/
theorem summable_powerTerm {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun pk : Nat.Primes × ℕ => powerTerm s pk.1 pk.2) := by
  apply Summable.of_norm_bounded
    ((summable_majorant hs).mul_left (s.re - 1 / 2)⁻¹)
  intro pk
  exact norm_powerTerm_le hs pk.1 pk.2

/-- Page 369, display 20. The even exponent subseries converges absolutely. -/
theorem summable_even {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun pk : Nat.Primes × ℕ => powerTerm s pk.1 (2 * pk.2)) := by
  have hi : Function.Injective (fun pk : Nat.Primes × ℕ => (pk.1, 2 * pk.2)) := by
    rintro ⟨p, k⟩ ⟨q, l⟩ h
    change (p, 2 * k) = (q, 2 * l) at h
    simp only [Prod.mk.injEq] at h
    have hkl : k = l := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h.2
    exact Prod.ext h.1 hkl
  change Summable ((fun pk : Nat.Primes × ℕ => powerTerm s pk.1 pk.2) ∘
    (fun pk : Nat.Primes × ℕ => (pk.1, 2 * pk.2)))
  exact Summable.comp_injective (summable_powerTerm hs) hi

/-- Page 369, display 20. At one prime the even powers give the first prime sum. -/
theorem prime_even {s : ℂ} (hs : 1 / 2 < s.re) (p : Nat.Primes) :
    (∑' k : ℕ, powerTerm s p (2 * k)) =
      (Real.log p : ℂ) / ((p : ℂ) ^ (2 * s) - 1) := by
  calc (∑' k : ℕ, powerTerm s p (2 * k)) =
      ∑' k : ℕ, (Real.log p : ℂ) / ((p : ℂ) ^ (2 * s)) ^ (k + 1) := by
        apply tsum_congr
        intro k
        unfold powerTerm
        congr 1
        rw [← Complex.cpow_nat_mul]
        congr 1
        push_cast
        ring
    _ = (Real.log p : ℂ) / ((p : ℂ) ^ (2 * s) - 1) := by
      apply PrimePowers95.geometric_full
      rw [norm_natCast_cpow_of_pos p.prop.pos]
      apply Real.one_lt_rpow (by exact_mod_cast p.prop.one_lt)
      norm_num [Complex.mul_re]
      linarith

/-- Page 369, display 20. The full local tail is the even part plus primeTerm. -/
theorem prime_local {s : ℂ} (hs : 1 / 2 < s.re) (p : Nat.Primes) :
    (∑' k : ℕ, powerTerm s p k) =
      (Real.log p : ℂ) / ((p : ℂ) ^ (2 * s) - 1) + L5.primeTerm s p := by
  simpa [powerTerm, L5.primeTerm, p.prop] using
    PrimePowers95.prime_split p.prop (show 0 < s.re by linarith)

/-- Page 369. Absolute convergence permits exchanging the printed two sums. -/
theorem gSeries_prime_first {s : ℂ} (hs : 1 / 2 < s.re) :
    gSeries s = ∑' p : Nat.Primes, ∑' k : ℕ, powerTerm s p k := by
  exact (summable_powerTerm hs).tsum_comm

/-- Page 369, equation 20, for every complex s in the printed half plane. -/
theorem g_identity {s : ℂ} (hs : 1 / 2 < s.re) :
    gSeries s = LSeries ↗Λ (2 * s) + ∑' n : ℕ, L5.primeTerm s n := by
  have hG := (summable_powerTerm hs).prod
  have hB : Summable (fun p : Nat.Primes =>
      (Real.log p : ℂ) / ((p : ℂ) ^ (2 * s) - 1)) :=
    (summable_even hs).prod.congr (fun p => prime_even hs p)
  have hC : Summable (fun p : Nat.Primes => L5.primeTerm s p) := by
    apply (hG.sub hB).congr
    intro p
    rw [prime_local hs p]
    ring
  have hsupport : Function.support (L5.primeTerm s) ⊆ {n : ℕ | n.Prime} := by
    intro n hn
    by_contra hnp
    change ¬ n.Prime at hnp
    apply hn
    simp [L5.primeTerm, hnp]
  have hs2 : 1 < (2 * s).re := by
    norm_num [Complex.mul_re]
    linarith
  calc gSeries s = ∑' p : Nat.Primes, ∑' k : ℕ, powerTerm s p k := gSeries_prime_first hs
    _ = ∑' p : Nat.Primes,
        ((Real.log p : ℂ) / ((p : ℂ) ^ (2 * s) - 1) + L5.primeTerm s p) := by
      apply tsum_congr
      intro p
      exact prime_local hs p
    _ = (∑' p : Nat.Primes, (Real.log p : ℂ) / ((p : ℂ) ^ (2 * s) - 1)) +
        ∑' p : Nat.Primes, L5.primeTerm s p := hB.tsum_add hC
    _ = LSeries ↗Λ (2 * s) + ∑' n : ℕ, L5.primeTerm s n := by
      rw [← PrimePowers95.vonMangoldt_prime_sum hs2]
      congr 1
      exact tsum_subtype_eq_of_support_subset hsupport

/-- Page 369, equation 20 in the lab's existing B and C notation. -/
theorem eq20 {σ : ℝ} (hσ : 1 / 2 < σ) (t : ℝ) :
    gSeries (L5.sAt σ t) = L5.dirB σ t + L5.primeC σ t := by
  apply g_identity
  simpa [L5.sAt] using hσ

/-- Page 369. A concrete point in the convergence half plane. -/
theorem series_instance :
    Summable (fun pk : Nat.Primes × ℕ => powerTerm (3 / 4) pk.1 pk.2) := by
  apply summable_powerTerm
  norm_num

end LeanLab.Kaniecki1995.Series20

#print axioms LeanLab.Kaniecki1995.Series20.summable_majorant
#print axioms LeanLab.Kaniecki1995.Series20.norm_powerTerm_le
#print axioms LeanLab.Kaniecki1995.Series20.summable_powerTerm

#print axioms LeanLab.Kaniecki1995.Series20.series_instance

#print axioms LeanLab.Kaniecki1995.Series20.summable_even

#print axioms LeanLab.Kaniecki1995.Series20.prime_even

#print axioms LeanLab.Kaniecki1995.Series20.prime_local

#print axioms LeanLab.Kaniecki1995.Series20.gSeries_prime_first

#print axioms LeanLab.Kaniecki1995.Series20.g_identity

#print axioms LeanLab.Kaniecki1995.Series20.eq20
