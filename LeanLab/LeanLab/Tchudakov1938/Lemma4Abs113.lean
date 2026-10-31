/- AI-written Lean code by OpenAI Codex, task113, 2026-10-26. Binary Goldbach is open. -/
import LeanLab.Tchudakov1938.PrimeValues113
import LeanLab.Tchudakov1938.Decomp113b
namespace LeanLab.Tchudakov1938.Lemma4Abs113
open LeanLab.Tchudakov1938.Decomp113 LeanLab.Tchudakov1938.PrimeValues113
/-- LEAF. P0064, page 28, last display in the Lemma 4 proof.
Prime power and coprime induction extend the prime bound to every modulus. -/
theorem coefficient_norm_scaled (m : ℕ) (q : ℕ+) :
    (Nat.totient (q : ℕ) : ℝ)^2 * ‖coefficient m q‖ ≤ Nat.gcd (q : ℕ) m := by
  have H : ∀ n : ℕ, ∀ hn : 0 < n,
      (n.totient : ℝ)^2 * ‖coefficient m ⟨n, hn⟩‖ ≤ Nat.gcd n m := by
    intro n
    induction n using Nat.recOnPosPrimePosCoprime with
    | zero => intro hn; omega
    | one =>
      intro hn
      change (Nat.totient 1 : ℝ)^2 * ‖coefficient m 1‖ ≤ Nat.gcd 1 m
      simp [coefficient_one]
    | prime_pow p k hp hk =>
      intro hn
      by_cases hk1 : k = 1
      · subst k
        simpa using coefficient_prime_norm_scaled ⟨p, hp.pos⟩ hp m
      · have hsq : ¬ Squarefree (p ^ k) := by
          rw [Nat.squarefree_pow_iff hp.ne_one hk.ne']
          simp [hk1]
        rw [coefficient_not_squarefree m ⟨p ^ k, hn⟩ hsq]
        simp
    | coprime a b ha hb hab iha ihb =>
      intro hn
      have ha0 : 0 < a := by omega
      have hb0 : 0 < b := by omega
      have hA := iha ha0
      have hB := ihb hb0
      have hcoeff : coefficient m ⟨a * b, hn⟩ =
          coefficient m ⟨a, ha0⟩ * coefficient m ⟨b, hb0⟩ :=
        lemma3 m ⟨a, ha0⟩ ⟨b, hb0⟩ hab
      have hd : Nat.gcd a m * Nat.gcd b m ∣ Nat.gcd (a * b) m := by
        apply Nat.dvd_gcd
        · exact Nat.mul_dvd_mul (Nat.gcd_dvd_left a m) (Nat.gcd_dvd_left b m)
        · exact (Nat.Coprime.of_dvd (Nat.gcd_dvd_left a m) (Nat.gcd_dvd_left b m) hab).mul_dvd_of_dvd_of_dvd
            (Nat.gcd_dvd_right a m) (Nat.gcd_dvd_right b m)
      have hgcd : Nat.gcd a m * Nat.gcd b m ≤ Nat.gcd (a * b) m :=
        Nat.le_of_dvd (Nat.gcd_pos_of_pos_left m (by positivity)) hd
      rw [hcoeff, Nat.totient_mul hab, Nat.cast_mul, mul_pow, norm_mul]
      calc (a.totient : ℝ)^2 * (b.totient : ℝ)^2 *
            (‖coefficient m ⟨a, ha0⟩‖ * ‖coefficient m ⟨b, hb0⟩‖)
          = ((a.totient : ℝ)^2 * ‖coefficient m ⟨a, ha0⟩‖) *
            ((b.totient : ℝ)^2 * ‖coefficient m ⟨b, hb0⟩‖) := by ring
        _ ≤ (Nat.gcd a m : ℝ) * Nat.gcd b m := mul_le_mul hA hB (by positivity) (by positivity)
        _ ≤ Nat.gcd (a * b) m := by exact_mod_cast hgcd
  exact H q q.pos

/-- P0064, page 28, last display. The norm bound with its totient denominator. -/
theorem coefficient_norm_le (m : ℕ) (q : ℕ+) :
    ‖coefficient m q‖ ≤ (Nat.gcd (q : ℕ) m : ℝ) / (Nat.totient (q : ℕ) : ℝ)^2 := by
  have hp : 0 < (Nat.totient (q : ℕ) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr q.pos
  rw [le_div_iff₀ (sq_pos_of_pos hp), mul_comm]
  exact coefficient_norm_scaled m q


open Filter Asymptotics
open LeanLab.Tchudakov1938.Decomp113b

/-- LEAF. P0064, page 29, inequality 2.
The coefficient norm is bounded by a constant times m log squared q divided by q squared. -/
theorem coefficient_norm_log_le (m : ℕ) (hm : 0 < m) (q : ℕ+) (hq : 2 ≤ (q : ℕ)) :
    ‖coefficient m q‖ ≤ (m : ℝ) / (Real.log 2 / 2)^2 * (Real.log (q : ℕ))^2 / (q : ℝ)^2 := by
  have hc : 0 < Real.log 2 / 2 := by positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast q.pos
  have hp : 0 < (Nat.totient (q : ℕ) : ℝ) := by exact_mod_cast Nat.totient_pos.mpr q.pos
  have hlog : 0 < Real.log (q : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < (q : ℕ)))
  have ht := totient_log_lower (q : ℕ) hq
  have hs : (Real.log 2 / 2)^2 * (q : ℝ)^2 ≤
      (Nat.totient (q : ℕ) : ℝ)^2 * (Real.log (q : ℕ))^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) ht 2
  have hgcd : (Nat.gcd (q : ℕ) m : ℝ) ≤ m := by exact_mod_cast Nat.gcd_le_right (q : ℕ) hm
  calc ‖coefficient m q‖ ≤ (Nat.gcd (q : ℕ) m : ℝ) / (Nat.totient (q : ℕ) : ℝ)^2 := coefficient_norm_le m q
    _ ≤ (m : ℝ) / (Nat.totient (q : ℕ) : ℝ)^2 := div_le_div_of_nonneg_right hgcd (by positivity)
    _ ≤ ((m : ℝ) * (Real.log (q : ℕ))^2) / ((Real.log 2 / 2)^2 * (q : ℝ)^2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have H := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ m by positivity)
      nlinarith
    _ = _ := by ring

/-- LEAF. P0064, page 29, convergence of the comparison series in inequality 2. -/
theorem summable_log_sq_div_sq : Summable (fun n : ℕ => Real.log n ^ 2 / (n : ℝ) ^ 2) := by
  apply summable_of_isBigO_nat (Real.summable_nat_rpow.mpr (by norm_num : (-3 / 2 : ℝ) < -1))
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 1/2) (by norm_num)).isBigO
  have hn := h.comp_tendsto tendsto_natCast_atTop_atTop
  have hm := hn.mul (isBigO_refl (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) atTop)
  have hp (n : ℕ) : (n : ℝ) ^ (1 / 2 : ℝ) * ((n : ℝ) ^ 2)⁻¹ = (n : ℝ)^(-3/2 : ℝ) := by
    rw [← div_eq_mul_inv, ← Real.rpow_two (n : ℝ)]
    rw [← Real.rpow_sub' (Nat.cast_nonneg n) (by norm_num : (1/2 : ℝ) - 2 ≠ 0)]
    norm_num
  simp only [Function.comp_apply, Real.rpow_two] at hm
  simp_rw [hp] at hm
  simpa only [div_eq_mul_inv] using hm


/-- LEAF. P0064, page 29, inequality 2. Absolute convergence for positive m. -/
theorem summable_norm_coefficient (m : ℕ) (hm : 0 < m) : Summable (fun q : ℕ+ => ‖coefficient m q‖) := by
  have hg : Summable (fun n : ℕ => Real.log (n + 1 : ℕ) ^ 2 / ((n + 1 : ℕ) : ℝ)^2) :=
    (summable_nat_add_iff 1).mpr summable_log_sq_div_sq
  have hf : Summable (fun n : ℕ => ‖coefficient m n.succPNat‖) := by
    apply (hg.mul_left ((m : ℝ) / (Real.log 2 / 2)^2)).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [norm_norm]
    simpa only [Nat.succPNat_coe, Nat.succ_eq_add_one, mul_div_assoc] using
      coefficient_norm_log_le m hm n.succPNat (by simpa using (by omega : 2 ≤ n + 1))
  exact Equiv.pnatEquivNat.symm.summable_iff.mp hf

/-- CITED. P0064, Lemma 4 part 1, page 28, with proof on page 29.
The paper uses positive Fourier indices m. -/
def lemma4AbsoluteStatement : Prop :=
  ∀ m : ℕ, 0 < m → Summable (fun q : ℕ+ => ‖coefficient m q‖)

/-- P0064, Lemma 4 part 1. Exact cited proposition assembled from the leaves. -/
theorem lemma4_absolute : lemma4AbsoluteStatement :=
  summable_norm_coefficient

/-- P0064, page 29, the complex coefficient series also converges. -/
theorem summable_coefficient (m : ℕ) (hm : 0 < m) :
    Summable (fun q : ℕ+ => coefficient m q) :=
  (summable_norm_iff).mp (summable_norm_coefficient m hm)

end LeanLab.Tchudakov1938.Lemma4Abs113
