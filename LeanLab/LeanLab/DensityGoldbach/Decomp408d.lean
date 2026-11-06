/-
Alsetri Theorem 1.1 through the shared explicit residue profile.
Source: https://arxiv.org/abs/2505.09648v3 pages 13 to 14.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.DensityGoldbach.Decomp408b
import LeanLab.DensityGoldbach.AlsetriFull

open Finset

namespace LeanLab.DensityGoldbach.Decomp408d

-- decidable instances for the finite filters over `A` used in the proof below
section

open scoped Classical

private lemma cutoff_iff (n p : ℕ) (hn : 0 < n) : 3 * p < 2 * n ↔ p ≤ (2 * n - 1) / 3 := by
  omega

private lemma half_primorial_eq (z : ℕ) (hz : 3 ≤ z) :
    primorial z = 2 * (primorial z / 2) := by
  have h2 : 2 ∣ primorial z := prime_dvd_primorial Nat.prime_two (by omega)
  exact (Nat.mul_div_cancel' h2).symm

private lemma totient_half_primorial (z : ℕ) (hz : 3 ≤ z) :
    (primorial z).totient = (primorial z / 2).totient := by
  obtain ⟨-, hodd, -, -⟩ := half_primorial_props hz
  have h : (2 * (primorial z / 2)).totient = (primorial z / 2).totient := by
    rw [Nat.totient_mul (Nat.coprime_two_left.mpr hodd), Nat.totient_two, one_mul]
  conv_lhs => rw [half_primorial_eq z hz]
  exact h

private lemma three_dvd_primorial (z : ℕ) (hz : 3 ≤ z) : 3 ∣ primorial z :=
  prime_dvd_primorial Nat.prime_three hz

/-- A prime dividing the half primorial is at most `z`. -/
private lemma prime_le_of_dvd_half {p z : ℕ} (hz : 3 ≤ z) (hp : p.Prime)
    (hm : p ∣ primorial z / 2) : p ≤ z := by
  refine (hp.dvd_primorial_iff).1 ?_
  exact (half_primorial_eq z hz) ▸ Dvd.dvd.mul_left hm 2

/-- The odd representative of a unit is coprime to the full primorial. -/
private lemma coprime_oddRepresentative {m : ℕ} [NeZero m] (hodd : Odd m) (b : ZMod m)
    (hb : IsUnit b) :
    Nat.Coprime (Profiles408.oddRepresentative m b) (2 * m) := by
  obtain ⟨-, haodd, ham⟩ := Profiles408.oddRepresentative_properties m hodd b
  have hbm : Nat.Coprime b.val m := by
    rw [← ZMod.isUnit_iff_coprime b.val m, ZMod.natCast_zmod_val]
    exact hb
  have ham' : Nat.Coprime (Profiles408.oddRepresentative m b) m := by
    unfold Profiles408.oddRepresentative
    split_ifs with h
    · simpa [h] using hbm
    · exact Nat.coprime_add_self_left.2 hbm
  have := ham'.mul_right (Nat.coprime_two_left.mpr haodd).symm
  simpa [Nat.mul_comm] using this

/-- The support property: outside the class `1 mod 3` the profile vanishes. -/
private lemma class_zero {δ : ℝ} {z n : ℕ} {A : Set ℕ} (hδ : 0 < δ) (hz : 3 ≤ z)
    (hsupport : ∀ a ∈ A, a % 3 = 1)
    (m : ℕ) [NeZero m] (hm : m = primorial z / 2) (b : ZMod m) (hb3 : b.val % 3 ≠ 1) :
    Profiles408.halfProfile A z n δ m b = 0 := by
  obtain ⟨-, hodd, -, hm3⟩ := half_primorial_props hz
  have hodd' : Odd m := hm ▸ hodd
  have hm3' : 3 ∣ m := hm ▸ hm3
  have hW2 : primorial z = 2 * m := by rw [hm]; exact half_primorial_eq z hz
  have hm_dvd : m ∣ primorial z := ⟨2, by rw [hW2]; ring⟩
  obtain ⟨-, -, ham⟩ := Profiles408.oddRepresentative_properties m hodd' b
  have hsum0 : (∑ p ∈ (Finset.range (n + 1)).filter
      (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z ∧
        3 * p < 2 * n), Real.log p) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨-, hpA, hpmod, -⟩ := hp
    have h1 : Nat.ModEq m (Profiles408.oddRepresentative m b) b.val := by
      show Profiles408.oddRepresentative m b % m = b.val % m
      rw [ham, Nat.mod_eq_of_lt (ZMod.val_lt b)]
    have h4 : Nat.ModEq m p b.val :=
      (Nat.ModEq.of_dvd hm_dvd hpmod).trans h1
    have h5 : Nat.ModEq 3 p b.val := Nat.ModEq.of_dvd hm3' h4
    have h6 : p % 3 = b.val % 3 := h5
    have h7 : p % 3 = 1 := hsupport p hpA
    rw [h7] at h6
    exact absurd h6.symm hb3
  simp only [Profiles408.halfProfile, Profiles408.primeProfile, hsum0, mul_zero, zero_sub]
  exact max_eq_right (by linarith)

private lemma class_nonneg {δ : ℝ} {z n : ℕ} {A : Set ℕ} (m : ℕ) [NeZero m] (b : ZMod m) :
    0 ≤ Profiles408.halfProfile A z n δ m b := by
  simp only [Profiles408.halfProfile, Profiles408.primeProfile]
  exact le_max_right _ _


/-! ### Elementary arithmetic for the profile factor -/

private lemma Y_le (n : ℕ) : 3 * ((2 * n - 1) / 3) ≤ 2 * n := by
  have := Nat.div_mul_le_self (2 * n - 1) 3
  omega

private lemma Y_le' (n : ℕ) : ((2 * n - 1) / 3) ≤ n :=
  (Nat.div_le_iff_le_mul (by norm_num : 0 < 3)).2 (by omega)

private lemma c0_nonneg (z n : ℕ) :
    (0 : ℝ) ≤ 3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)) := by
  have : (0:ℝ) ≤ ((primorial z).totient : ℝ) := Nat.cast_nonneg _
  positivity

/-- The profile factor times the principal term of the class sum is at most `1`. -/
private lemma c0_principal (z n : ℕ) (hn : 0 < n) :
    (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
      * ((((2 * n - 1) / 3 : ℕ) : ℝ) / ((primorial z).totient : ℝ)) ≤ 1 := by
  have hφ : (0:ℝ) < ((primorial z).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 (primorial_pos z)
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hY : 3 * (((2 * n - 1) / 3 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast Y_le n
  have e : (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
      * ((((2 * n - 1) / 3 : ℕ) : ℝ) / ((primorial z).totient : ℝ))
      = 3 * (((2 * n - 1) / 3 : ℕ) : ℝ) / (2 * (n : ℝ)) := by
    field_simp
  rw [e, div_le_one (by positivity)]
  exact hY

/-- The profile factor times the error term of the class sum is a relative error. -/
private lemma c0_error (z n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hn : 0 < n) :
    (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
      * (ε * (((2 * n - 1) / 3 : ℕ) : ℝ)) ≤ ε * ((primorial z).totient : ℝ) := by
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hY : 3 * (((2 * n - 1) / 3 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast Y_le n
  have hφ : (0:ℝ) ≤ ((primorial z).totient : ℝ) := Nat.cast_nonneg _
  have e : (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
      * (ε * (((2 * n - 1) / 3 : ℕ) : ℝ))
      = (3 * (((2 * n - 1) / 3 : ℕ) : ℝ) / (2 * (n : ℝ)))
        * (ε * ((primorial z).totient : ℝ)) := by
    field_simp
  rw [e]
  have h1 : 3 * (((2 * n - 1) / 3 : ℕ) : ℝ) / (2 * (n : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hY
  calc (3 * (((2 * n - 1) / 3 : ℕ) : ℝ) / (2 * (n : ℝ)))
        * (ε * ((primorial z).totient : ℝ))
      ≤ 1 * (ε * ((primorial z).totient : ℝ)) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg hε hφ)
    _ = ε * ((primorial z).totient : ℝ) := one_mul _

/-- The profile factor times `log z` is at most `1` once `n` is large. -/
private lemma c0_log (z n : ℕ) (hz : 1 ≤ z) (hn : 0 < n)
    (hbig : 3 * ((primorial z).totient : ℝ) * z ≤ 2 * n) :
    (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ))) * Real.log (z : ℝ) ≤ 1 := by
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hz0 : (0:ℝ) < (z:ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hlog : Real.log (z : ℝ) ≤ z := by
    have := Real.log_le_sub_one_of_pos hz0
    linarith
  have hφ : (0:ℝ) ≤ ((primorial z).totient : ℝ) := Nat.cast_nonneg _
  have e : (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ))) * Real.log (z : ℝ)
      = (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ))) * Real.log (z : ℝ) := rfl
  have h1a : (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ))) * Real.log (z : ℝ)
      ≤ (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ))) * z :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have h1b : (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ))) * z
      = (3 * ((primorial z).totient : ℝ) * z) / (2 * (n : ℝ)) := by ring
  have h1 : (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ))) * Real.log (z : ℝ)
      ≤ (3 * ((primorial z).totient : ℝ) * z) / (2 * (n : ℝ)) := by linarith
  have h2 : (3 * ((primorial z).totient : ℝ) * z) / (2 * (n : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hbig
  linarith

/-! ### The upper bound `f b ≤ 1` -/

private lemma class_le_one {δ : ℝ} {z n : ℕ} {A : Set ℕ}
    (hδ : 0 < δ) (hz : 3 ≤ z) (hA : A ⊆ P)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hεφ : ε * ((primorial z).totient : ℝ) ≤ δ / 8)
    (n₀ : ℕ)
    (hn₀ : ∀ N : ℕ, n₀ ≤ N → ∀ a : ℕ, Nat.Coprime a (primorial z) →
      |(∑ p ∈ (Finset.range (N + 1)).filter
          (fun p => p.Prime ∧ p % primorial z = a % primorial z), Real.log p)
        - (N : ℝ) / ((primorial z).totient : ℝ)| ≤ ε * N)
    (m : ℕ) [NeZero m] (hm : m = primorial z / 2)
    (hn1 : 1 ≤ n) (hnY : n₀ ≤ (2 * n - 1) / 3)
    (hbig : 3 * ((primorial z).totient : ℝ) * z ≤ 2 * n)
    (b : ZMod m) : Profiles408.halfProfile A z n δ m b ≤ 1 := by
  obtain ⟨hmpos, hodd, -, hm3⟩ := half_primorial_props hz
  have hodd' : Odd m := hm ▸ hodd
  have hm3' : 3 ∣ m := hm ▸ hm3
  have hW2 : primorial z = 2 * m := by rw [hm]; exact half_primorial_eq z hz
  have hn0 : 0 < n := hn1
  have hPa : ∀ p ∈ A, p.Prime := fun p hp => by
    simpa only [P, Set.mem_setOf_eq] using hA hp
  by_cases hb : IsUnit b
  case pos =>
    set a : ℕ := Profiles408.oddRepresentative m b with hadef
    have ha_lt : a < primorial z := by
      have := (Profiles408.oddRepresentative_properties m hodd' b).1
      rw [hW2]; exact this
    have ha_cop : Nat.Coprime a (primorial z) := hW2 ▸ coprime_oddRepresentative hodd' b hb
    have hsub : (Finset.range (n + 1)).filter
          (fun p => p ∈ A ∧ p % primorial z = a % primorial z ∧ 3 * p < 2 * n)
        ⊆ (Finset.range ((2 * n - 1) / 3 + 1)).filter
          (fun p => p.Prime ∧ p % primorial z = a % primorial z) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
      obtain ⟨hpn, hpA, hpmod, hplt⟩ := hp
      have hple : p ≤ (2 * n - 1) / 3 := (cutoff_iff n p hn0).1 hplt
      exact ⟨by omega, hPa p hpA, hpmod⟩
    have hSle : (∑ p ∈ (Finset.range (n + 1)).filter
          (fun p => p ∈ A ∧ p % primorial z = a % primorial z ∧ 3 * p < 2 * n), Real.log p)
        ≤ ∑ p ∈ (Finset.range ((2 * n - 1) / 3 + 1)).filter
            (fun p => p.Prime ∧ p % primorial z = a % primorial z), Real.log p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => Real.log_natCast_nonneg p)
    have hθ := hn₀ ((2 * n - 1) / 3) hnY a ha_cop
    rw [abs_le] at hθ
    obtain ⟨-, hθ2⟩ := hθ
    have hSc : (∑ p ∈ (Finset.range (n + 1)).filter
          (fun p => p ∈ A ∧ p % primorial z = a % primorial z ∧ 3 * p < 2 * n), Real.log p)
        ≤ (((2 * n - 1) / 3 : ℕ) : ℝ) / ((primorial z).totient : ℝ)
          + ε * (((2 * n - 1) / 3 : ℕ) : ℝ) := by linarith
    have hfac : (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
        * (∑ p ∈ (Finset.range (n + 1)).filter
            (fun p => p ∈ A ∧ p % primorial z = a % primorial z ∧ 3 * p < 2 * n),
            Real.log p) - δ / 8 ≤ 1 := by
      have hc0 := c0_nonneg z n
      have hmul := mul_le_mul_of_nonneg_left hSc hc0
      have hdist : (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
          * ((((2 * n - 1) / 3 : ℕ) : ℝ) / ((primorial z).totient : ℝ)
            + ε * (((2 * n - 1) / 3 : ℕ) : ℝ))
          = (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
              * ((((2 * n - 1) / 3 : ℕ) : ℝ) / ((primorial z).totient : ℝ))
            + (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
              * (ε * (((2 * n - 1) / 3 : ℕ) : ℝ)) := by ring
      have hA1 := c0_principal z n hn0
      have hA2 := c0_error z n ε hε0 hn0
      linarith
    calc Profiles408.halfProfile A z n δ m b
        = max ((3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
            * (∑ p ∈ (Finset.range (n + 1)).filter
                (fun p => p ∈ A ∧ p % primorial z = a % primorial z ∧ 3 * p < 2 * n),
                Real.log p) - δ / 8) 0 := by
          simp only [Profiles408.halfProfile, Profiles408.primeProfile, hadef]
      _ ≤ max 1 0 := max_le_max hfac le_rfl
      _ = 1 := by norm_num
  case neg =>
    have hg : Nat.gcd b.val m ≠ 1 := by
      intro hgc
      apply hb
      rw [← ZMod.natCast_zmod_val b, ZMod.isUnit_iff_coprime b.val m]
      exact hgc
    obtain ⟨p₀, hp₀prime, hp₀dvd⟩ := Nat.exists_prime_and_dvd hg
    have hp₀m : p₀ ∣ m := hp₀dvd.trans (Nat.gcd_dvd_right _ _)
    have hp₀b : p₀ ∣ b.val := hp₀dvd.trans (Nat.gcd_dvd_left _ _)
    have hp₀z : p₀ ≤ z := prime_le_of_dvd_half hz hp₀prime (hm ▸ hp₀m)
    have hp₀W : p₀ ∣ primorial z := prime_dvd_primorial hp₀prime hp₀z
    have hp₀a : p₀ ∣ Profiles408.oddRepresentative m b := by
      unfold Profiles408.oddRepresentative
      split_ifs with h
      · exact hp₀b
      · exact dvd_add hp₀b hp₀m
    have heq : ∀ p ∈ (Finset.range (n + 1)).filter
        (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
          ∧ 3 * p < 2 * n), p = p₀ := by
      intro p hp
      simp only [Finset.mem_filter] at hp
      have hmod : p % primorial z = Profiles408.oddRepresentative m b % primorial z := hp.2.2.1
      have h0 : p % p₀ = 0 := by
        rw [← Nat.mod_mod_of_dvd _ hp₀W, hmod, Nat.mod_mod_of_dvd _ hp₀W,
          Nat.mod_eq_zero_of_dvd hp₀a]
      exact ((Nat.prime_dvd_prime_iff_eq hp₀prime (hPa p hp.2.1)).1
        (Nat.dvd_of_mod_eq_zero h0)).symm
    have hcard : ((Finset.range (n + 1)).filter
        (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
          ∧ 3 * p < 2 * n)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro x hx y hy
      rw [heq x hx, heq y hy]
    have hSz : (∑ p ∈ (Finset.range (n + 1)).filter
          (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
            ∧ 3 * p < 2 * n), Real.log p) ≤ Real.log (z : ℝ) := by
      have h1 : (∑ p ∈ (Finset.range (n + 1)).filter
          (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
            ∧ 3 * p < 2 * n), Real.log p)
          ≤ (((Finset.range (n + 1)).filter
            (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
              ∧ 3 * p < 2 * n)).card : ℝ) * Real.log (p₀ : ℝ) := by
        calc (∑ p ∈ (Finset.range (n + 1)).filter
            (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
              ∧ 3 * p < 2 * n), Real.log p)
            ≤ ∑ _p ∈ (Finset.range (n + 1)).filter
              (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
                ∧ 3 * p < 2 * n), Real.log (p₀ : ℝ) := by
              apply Finset.sum_le_sum
              intro p hp
              rw [heq p hp]
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
      have h2 : ((((Finset.range (n + 1)).filter
          (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
            ∧ 3 * p < 2 * n)).card : ℕ) : ℝ) * Real.log (p₀ : ℝ) ≤ Real.log (p₀ : ℝ) := by
        have hc : (((Finset.range (n + 1)).filter
            (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
              ∧ 3 * p < 2 * n)).card : ℝ) ≤ 1 := by exact_mod_cast hcard
        nlinarith [Real.log_natCast_nonneg p₀]
      have h3 : Real.log (p₀ : ℝ) ≤ Real.log (z : ℝ) := by
        apply Real.log_le_log (by exact_mod_cast hp₀prime.pos)
        exact_mod_cast hp₀z
      linarith
    have hfac : (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
        * (∑ p ∈ (Finset.range (n + 1)).filter
            (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
              ∧ 3 * p < 2 * n), Real.log p) - δ / 8 ≤ 1 := by
      have hc0 := c0_nonneg z n
      have hmul := mul_le_mul_of_nonneg_left hSz hc0
      have hA1 := c0_log z n (by omega) hn0 hbig
      linarith
    calc Profiles408.halfProfile A z n δ m b
        = max ((3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
            * (∑ p ∈ (Finset.range (n + 1)).filter
                (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b
                  % primorial z ∧ 3 * p < 2 * n), Real.log p) - δ / 8) 0 := by
          simp only [Profiles408.halfProfile, Profiles408.primeProfile]
      _ ≤ max 1 0 := max_le_max hfac le_rfl
      _ = 1 := by norm_num


/-! ### Counting the reduced residue classes modulo the primorial -/

private lemma card_unitsMod_eq (m : ℕ) [NeZero m] : #(unitsMod m) = m.totient := by
  rw [unitsMod, ← ZMod.card_units_eq_totient, ← Fintype.card_coe]
  exact Fintype.card_congr
    { toFun := fun u => IsUnit.unit (mem_filter.1 u.2).2
      invFun := fun u => ⟨(u : ZMod m), mem_filter.2 ⟨mem_univ _, u.isUnit⟩⟩
      left_inv := fun u => by simp
      right_inv := fun u => by ext; simp }

/-- The odd representative of a unit is odd and coprime to the primorial. -/
private lemma oddRepresentative_mem_props {m : ℕ} [NeZero m] (hodd : Odd m) (b : ZMod m) :
    Profiles408.oddRepresentative m b < 2 * m ∧ Odd (Profiles408.oddRepresentative m b) := by
  obtain ⟨h1, h2, -⟩ := Profiles408.oddRepresentative_properties m hodd b
  exact ⟨h1, h2⟩

/-- A reduced residue modulo `2m` comes from exactly one unit modulo `m`. -/
private lemma exists_unique_class {m : ℕ} [NeZero m] (hodd : Odd m) (hmpos : 0 < m)
    {p : ℕ} (hpodd : Odd p) (hcop : Nat.Coprime p (2 * m)) :
    ∃! b : ZMod m, b ∈ unitsMod m ∧ p % (2 * m) = Profiles408.oddRepresentative m b % (2 * m) := by
  have hm2 : 0 < 2 * m := by omega
  have hrlt : p % (2 * m) < 2 * m := Nat.mod_lt _ hm2
  have hrodd : Odd (p % (2 * m)) := by
    rw [Nat.odd_iff] at hpodd ⊢
    rw [Nat.mod_mod_of_dvd p (b := 2 * m) (dvd_mul_right 2 m)]
    exact hpodd
  have hrcop : Nat.Coprime (p % (2 * m)) (2 * m) :=
    (ZMod.coprime_mod_iff_coprime p (2 * m)).2 hcop
  have hrcopm : Nat.Coprime (p % (2 * m)) m := hrcop.coprime_dvd_right (dvd_mul_left m 2)
  have hb₀val : (((p % (2 * m) : ℕ)) : ZMod m).val = (p % (2 * m)) % m :=
    ZMod.val_natCast m _
  have hb₀unit : (((p % (2 * m) : ℕ)) : ZMod m) ∈ unitsMod m := by
    rw [unitsMod, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (ZMod.isUnit_iff_coprime (p % (2 * m)) m).2 hrcopm⟩
  have hdiv : (p % (2 * m)) / m = 0 ∨ (p % (2 * m)) / m = 1 := by
    have h : (p % (2 * m)) / m < 2 := (Nat.div_lt_iff_lt_mul hmpos).2 (by omega)
    rcases Nat.eq_zero_or_pos ((p % (2 * m)) / m) with h0 | hpos
    · exact Or.inl h0
    · exact Or.inr (by omega)
  have hdec : p % (2 * m) = (((p % (2 * m) : ℕ)) : ZMod m).val + m * ((p % (2 * m)) / m) := by
    have h2 : m * ((p % (2 * m)) / m) + (((p % (2 * m) : ℕ)) : ZMod m).val = p % (2 * m) := by
      have h3 := Nat.div_add_mod (p % (2 * m)) m
      rw [hb₀val]
      linarith
    linarith
  have hb₀odd : Profiles408.oddRepresentative m (((p % (2 * m) : ℕ)) : ZMod m) = p % (2 * m) := by
    unfold Profiles408.oddRepresentative
    split_ifs with h
    · rcases hdiv with hq | hq
      · rw [hq, Nat.mul_zero, add_zero] at hdec
        linarith
      · exfalso
        rw [hq, Nat.mul_one] at hdec
        have he : Even (p % (2 * m)) := hdec ▸ h.add_odd hodd
        exact (Nat.not_odd_iff_even).mpr he hrodd
    · rcases hdiv with hq | hq
      · rw [hq, Nat.mul_zero, add_zero] at hdec
        exact absurd (hdec ▸ hrodd) h
      · rw [hq, Nat.mul_one] at hdec
        linarith
  refine ⟨(((p % (2 * m) : ℕ)) : ZMod m), ⟨hb₀unit, ?_⟩, ?_⟩
  · rw [hb₀odd, Nat.mod_eq_of_lt hrlt]
  · intro b hb
    obtain ⟨-, hbeq⟩ := hb
    have h1 : Profiles408.oddRepresentative m b < 2 * m :=
      (Profiles408.oddRepresentative_properties m hodd b).1
    have h2 : p % (2 * m) = Profiles408.oddRepresentative m b := by
      rw [hbeq, Nat.mod_eq_of_lt h1]
    have h3 : Profiles408.oddRepresentative m b % m = b.val :=
      (Profiles408.oddRepresentative_properties m hodd b).2.2
    have h4 : b.val = (((p % (2 * m) : ℕ)) : ZMod m).val := by
      rw [← h3, ← h2, ← hb₀val]
    exact ZMod.val_injective m h4

/-- The class sum at a single prime: exactly one unit class contains it. -/
private lemma units_class_sum {z m : ℕ} [NeZero m] (hz : 3 ≤ z)
    (hm : m = primorial z / 2) {p : ℕ} (hpodd : Odd p) :
    (∑ b ∈ unitsMod m, (if p % primorial z = Profiles408.oddRepresentative m b % primorial z
        then Real.log p else 0))
      = if Nat.Coprime p (primorial z) then Real.log p else 0 := by
  obtain ⟨hmpos, hodd, -, hm3⟩ := half_primorial_props hz
  have hodd' : Odd m := hm ▸ hodd
  have hW2 : primorial z = 2 * m := by rw [hm]; exact half_primorial_eq z hz
  by_cases hc : Nat.Coprime p (primorial z)
  · obtain ⟨b₀, ⟨hb₀mem, hb₀eq⟩, huniq⟩ :=
      exists_unique_class hodd' (hm ▸ hmpos) hpodd (hW2 ▸ hc)
    rw [if_pos hc]
    have hsingle : (∑ b ∈ unitsMod m, (if p % primorial z
          = Profiles408.oddRepresentative m b % primorial z then Real.log (p : ℝ) else 0))
        = (if p % primorial z = Profiles408.oddRepresentative m b₀ % primorial z
          then Real.log (p : ℝ) else 0) := by
      refine Finset.sum_eq_single_of_mem b₀ hb₀mem ?_
      intro b hb hne
      rw [if_neg]
      intro hcontra
      exact hne (huniq b ⟨hb, hW2 ▸ hcontra⟩)
    rw [hsingle, if_pos (hW2.symm ▸ hb₀eq)]
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [if_neg]
    intro hcontra
    apply hc
    rw [unitsMod, Finset.mem_filter] at hb
    have hcop := coprime_oddRepresentative hodd' b hb.2
    have hlt : Profiles408.oddRepresentative m b < 2 * m :=
      (Profiles408.oddRepresentative_properties m hodd' b).1
    have hcontra' : p % (2 * m) = Profiles408.oddRepresentative m b % (2 * m) := hW2 ▸ hcontra
    have hmod : p % (2 * m) = Profiles408.oddRepresentative m b := by
      rw [hcontra', Nat.mod_eq_of_lt hlt]
    have hkey : Nat.Coprime (p % primorial z) (primorial z) := by
      rw [hW2, hmod]
      exact hcop
    exact (ZMod.coprime_mod_iff_coprime p (primorial z)).1 hkey

/-- The total profile mass is the logarithmic mass of `A` on the primes coprime to the
primorial. -/
private lemma sum_units_eq {z n : ℕ} {A : Set ℕ} (hz : 3 ≤ z) (hA : A ⊆ P)
    (hsupport : ∀ a ∈ A, a % 3 = 1) (m : ℕ) [NeZero m] (hm : m = primorial z / 2) :
    (∑ b ∈ unitsMod m, (∑ p ∈ (Finset.range (n + 1)).filter
        (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
          ∧ 3 * p < 2 * n), Real.log p))
      = ∑ p ∈ (Finset.range (n + 1)).filter
          (fun p => p ∈ A ∧ 3 * p < 2 * n ∧ Nat.Coprime p (primorial z)), Real.log p := by
  have hPa : ∀ p ∈ A, p.Prime := fun p hp => by
    simpa only [P, Set.mem_setOf_eq] using hA hp
  have step1 : ∀ b ∈ unitsMod m, (∑ p ∈ (Finset.range (n + 1)).filter
        (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
          ∧ 3 * p < 2 * n), Real.log p)
      = ∑ p ∈ Finset.range (n + 1),
          (if (p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
            ∧ 3 * p < 2 * n) then Real.log p else 0) := by
    intro b _
    rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  have hper : ∀ p ∈ Finset.range (n + 1),
      (∑ b ∈ unitsMod m, (if (p ∈ A ∧ p % primorial z
          = Profiles408.oddRepresentative m b % primorial z ∧ 3 * p < 2 * n)
        then Real.log p else 0))
      = (if (p ∈ A ∧ 3 * p < 2 * n ∧ Nat.Coprime p (primorial z)) then Real.log p else 0) := by
    intro p _
    by_cases hc0 : (p ∈ A ∧ 3 * p < 2 * n)
    · have hpodd : Odd p := by
        rcases (hPa p hc0.1).eq_two_or_odd' with h2 | ho
        · exfalso
          have h3 : p % 3 = 1 := hsupport p hc0.1
          rw [h2] at h3
          omega
        · exact ho
      have hrw : ∀ b ∈ unitsMod m, (if (p ∈ A ∧ p % primorial z
            = Profiles408.oddRepresentative m b % primorial z ∧ 3 * p < 2 * n)
          then Real.log p else 0)
          = (if (p % primorial z = Profiles408.oddRepresentative m b % primorial z)
            then Real.log p else 0) := by
        intro b _
        by_cases h : p % primorial z = Profiles408.oddRepresentative m b % primorial z
        · rw [if_pos ⟨hc0.1, h, hc0.2⟩, if_pos h]
        · rw [if_neg (by intro hcon; exact h hcon.2.1), if_neg h]
      rw [Finset.sum_congr rfl hrw, units_class_sum hz hm hpodd]
      by_cases hc : Nat.Coprime p (primorial z)
      · rw [if_pos hc, if_pos ⟨hc0.1, hc0.2, hc⟩]
      · rw [if_neg hc, if_neg (by intro hcon; exact hc hcon.2.2)]
    · have hzero : (∑ b ∈ unitsMod m, (if (p ∈ A ∧ p % primorial z
            = Profiles408.oddRepresentative m b % primorial z ∧ 3 * p < 2 * n)
          then Real.log (p : ℝ) else 0)) = 0 := by
        refine Finset.sum_eq_zero fun b _ => ?_
        rw [if_neg]
        intro hcon
        exact hc0 ⟨hcon.1, hcon.2.2⟩
      rw [hzero, if_neg (by intro hcon; exact hc0 ⟨hcon.1, hcon.2.1⟩)]
  rw [Finset.sum_congr rfl hper, Finset.sum_filter]

/-- The final numerical comparison of the mass lower bound. -/
private lemma mass_arith {δ ε' κ : ℝ} (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8)
    (hε'0 : 0 ≤ ε') (hε' : ε' ≤ δ / 16) (hκ0 : 0 ≤ κ) (hκ : κ ≤ δ / 64) :
    1 / 4 < (1 - κ) * (1 / 2 + δ / 2) * (1 - ε') / 2 - κ - δ / 8 := by
  have h1 : κ * ε' ≤ (δ / 64) * (δ / 16) := by
    apply mul_le_mul hκ hε' hε'0 (by linarith)
  have h2 : κ * δ ≤ (δ / 64) * δ := by
    apply mul_le_mul_of_nonneg_right hκ hδ.le
  have h3 : ε' * δ ≤ (δ / 16) * δ := by
    apply mul_le_mul_of_nonneg_right hε' hδ.le
  have hδ2 : δ ^ 2 ≤ (1 / 8) * δ := by nlinarith
  nlinarith [sq_nonneg δ, mul_nonneg hδ.le hδ.le]

/-- The profile mass exceeds a quarter of `φ(m)`. -/
private lemma mass {δ : ℝ} {z : ℕ} {A : Set ℕ}
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8) (hz : 3 ≤ z) (hA : A ⊆ P)
    (hsupport : ∀ a ∈ A, a % 3 = 1)
    (ε' κ : ℝ) (hε'0 : 0 < ε') (hε' : ε' ≤ δ / 16) (hκ0 : 0 ≤ κ) (hκ : κ ≤ δ / 64)
    (Y₀ : ℕ)
    (hY₀ : ∀ X : ℕ, Y₀ ≤ X →
      (1 / 2 + δ / 2) * (1 - ε') * X / 2 ≤
        ∑ p ∈ (Finset.range (X + 1)).filter (fun p => p ∈ A), Real.log p)
    (m : ℕ) [NeZero m] (hm : m = primorial z / 2)
    (n : ℕ) (hn1 : 1 ≤ n) (hnY : Y₀ ≤ (2 * n - 1) / 3)
    (hcard1 : ((primorial z).totient : ℝ) * (1 - κ) ≤
      (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ))) * (((2 * n - 1) / 3 : ℕ) : ℝ))
    (hcard2 : (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ))) * (Real.log 4 * z)
      ≤ ((primorial z).totient : ℝ) * κ) :
    (m.totient : ℝ) / 4 < ∑ b ∈ unitsMod m, Profiles408.halfProfile A z n δ m b := by
  obtain ⟨hmpos, hodd, -, hm3⟩ := half_primorial_props hz
  have hPa : ∀ p ∈ A, p.Prime := fun p hp => by
    simpa only [P, Set.mem_setOf_eq] using hA hp
  have hφpos : (0 : ℝ) < ((primorial z).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 (primorial_pos z)
  have htot : (m.totient : ℝ) = ((primorial z).totient : ℝ) := by
    rw [hm, totient_half_primorial z hz]
  have hc0 : (0 : ℝ) ≤ 3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)) := c0_nonneg z n
  -- the sum of the class sums, via the identity
  have hid := sum_units_eq (n := n) hz hA hsupport m hm
  -- small primes: the non-reduced classes contribute at most `θ z`
  have hsmall : (∑ p ∈ (Finset.range ((2 * n - 1) / 3 + 1)).filter
        (fun p => p ∈ A ∧ ¬ Nat.Coprime p (primorial z)), Real.log p) ≤ Real.log 4 * z := by
    have hsub : (Finset.range ((2 * n - 1) / 3 + 1)).filter
          (fun p => p ∈ A ∧ ¬ Nat.Coprime p (primorial z))
        ⊆ (Finset.range (z + 1)).filter Nat.Prime := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
      obtain ⟨-, hpA, hnc⟩ := hp
      have hpp : p.Prime := hPa p hpA
      have hgne : Nat.gcd p (primorial z) ≠ 1 := by
        intro h
        exact hnc (Nat.coprime_iff_gcd_eq_one.mpr h)
      have hgcd1 : 1 ≤ Nat.gcd p (primorial z) :=
        Nat.gcd_pos_of_pos_right p (primorial_pos z)
      obtain ⟨q, hqprime, hqdvd⟩ := Nat.exists_prime_and_dvd hgne
      have hqp : q = p :=
        (Nat.prime_dvd_prime_iff_eq hqprime hpp).1 (hqdvd.trans (Nat.gcd_dvd_left _ _))
      have hpW : p ∣ primorial z := by
        rw [← hqp]
        exact hqdvd.trans (Nat.gcd_dvd_right _ _)
      have hzle : p ≤ z := (hpp.dvd_primorial_iff).1 hpW
      exact ⟨by omega, hpp⟩
    calc (∑ p ∈ (Finset.range ((2 * n - 1) / 3 + 1)).filter
          (fun p => p ∈ A ∧ ¬ Nat.Coprime p (primorial z)), Real.log p)
        ≤ ∑ p ∈ (Finset.range (z + 1)).filter Nat.Prime, Real.log p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => Real.log_natCast_nonneg p)
      _ ≤ Real.log 4 * z := LeanLab.HardyLittlewood1923.theta_le z
  -- split the coprime part off the total mass at scale `(2n-1)/3`
  have hsplit : (∑ p ∈ (Finset.range ((2 * n - 1) / 3 + 1)).filter
        (fun p => p ∈ A ∧ Nat.Coprime p (primorial z)), Real.log p)
      = (∑ p ∈ (Finset.range ((2 * n - 1) / 3 + 1)).filter (fun p => p ∈ A), Real.log p)
        - (∑ p ∈ (Finset.range ((2 * n - 1) / 3 + 1)).filter
            (fun p => p ∈ A ∧ ¬ Nat.Coprime p (primorial z)), Real.log p) := by
    have e1 : (∑ p ∈ (Finset.range ((2 * n - 1) / 3 + 1)).filter
          (fun p => p ∈ A ∧ Nat.Coprime p (primorial z)), Real.log p)
        = ∑ p ∈ Finset.range ((2 * n - 1) / 3 + 1),
            (if (p ∈ A ∧ Nat.Coprime p (primorial z)) then Real.log (p : ℝ) else 0) :=
      Finset.sum_filter ..
    have e2 : (∑ p ∈ (Finset.range ((2 * n - 1) / 3 + 1)).filter (fun p => p ∈ A),
          Real.log p)
        = ∑ p ∈ Finset.range ((2 * n - 1) / 3 + 1),
            (if (p ∈ A) then Real.log (p : ℝ) else 0) := Finset.sum_filter ..
    have e3 : (∑ p ∈ (Finset.range ((2 * n - 1) / 3 + 1)).filter
          (fun p => p ∈ A ∧ ¬ Nat.Coprime p (primorial z)), Real.log p)
        = ∑ p ∈ Finset.range ((2 * n - 1) / 3 + 1),
            (if (p ∈ A ∧ ¬ Nat.Coprime p (primorial z)) then Real.log (p : ℝ) else 0) :=
      Finset.sum_filter ..
    rw [e1, e2, e3, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hA' : p ∈ A
    · by_cases hc : Nat.Coprime p (primorial z)
      · rw [if_pos ⟨hA', hc⟩, if_pos hA', if_neg (by intro h; exact h.2 hc)]
        ring
      · rw [if_neg (by intro h; exact hc h.2), if_pos hA', if_pos ⟨hA', hc⟩]
        ring
    · rw [if_neg (by intro h; exact hA' h.1), if_neg hA', if_neg (by intro h; exact hA' h.1)]
      ring
  -- the mass at scale `(2n-1)/3`, then reduced modulo the primorial
  have hθ := hY₀ ((2 * n - 1) / 3) hnY
  have hbig : (∑ p ∈ (Finset.range ((2 * n - 1) / 3 + 1)).filter
        (fun p => p ∈ A ∧ Nat.Coprime p (primorial z)), Real.log p) ≥
      (1 / 2 + δ / 2) * (1 - ε') * (((2 * n - 1) / 3 : ℕ) : ℝ) / 2 - Real.log 4 * z := by
    rw [hsplit]; linarith
  -- compare with the sum over the unit classes
  have hsub2 : (Finset.range ((2 * n - 1) / 3 + 1)).filter
        (fun p => p ∈ A ∧ Nat.Coprime p (primorial z))
      ⊆ (Finset.range (n + 1)).filter
        (fun p => p ∈ A ∧ 3 * p < 2 * n ∧ Nat.Coprime p (primorial z)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    obtain ⟨h1, h2, h3⟩ := hp
    have hYle : (2 * n - 1) / 3 ≤ n := Y_le' n
    refine ⟨by omega, h2, ?_, h3⟩
    exact (cutoff_iff n p hn1).2 (by omega)
  have hmono : (∑ p ∈ (Finset.range ((2 * n - 1) / 3 + 1)).filter
        (fun p => p ∈ A ∧ Nat.Coprime p (primorial z)), Real.log p)
      ≤ ∑ b ∈ unitsMod m, (∑ p ∈ (Finset.range (n + 1)).filter
        (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
          ∧ 3 * p < 2 * n), Real.log p) := by
    rw [hid]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun p _ _ => Real.log_natCast_nonneg p)
  -- assemble
  have hstep1 : (∑ b ∈ unitsMod m, ((3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
        * (∑ p ∈ (Finset.range (n + 1)).filter
          (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
            ∧ 3 * p < 2 * n), Real.log p) - δ / 8))
      ≤ ∑ b ∈ unitsMod m, Profiles408.halfProfile A z n δ m b := by
    refine Finset.sum_le_sum fun b _ => ?_
    simp only [Profiles408.halfProfile, Profiles408.primeProfile]
    exact le_max_left _ _
  have hstep2 : (∑ b ∈ unitsMod m, ((3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
        * (∑ p ∈ (Finset.range (n + 1)).filter
          (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
            ∧ 3 * p < 2 * n), Real.log p) - δ / 8))
      = (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
          * (∑ b ∈ unitsMod m, (∑ p ∈ (Finset.range (n + 1)).filter
            (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
              ∧ 3 * p < 2 * n), Real.log p))
        - (δ / 8) * (m.totient : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const, card_unitsMod_eq, nsmul_eq_mul]
    ring
  have hmain : (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
      * ((1 / 2 + δ / 2) * (1 - ε') * (((2 * n - 1) / 3 : ℕ) : ℝ) / 2 - Real.log 4 * z)
      - (δ / 8) * (m.totient : ℝ)
      ≤ ∑ b ∈ unitsMod m, Profiles408.halfProfile A z n δ m b := by
    have hmul : (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
        * ((1 / 2 + δ / 2) * (1 - ε') * (((2 * n - 1) / 3 : ℕ) : ℝ) / 2 - Real.log 4 * z)
        ≤ (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
          * (∑ b ∈ unitsMod m, (∑ p ∈ (Finset.range (n + 1)).filter
            (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
              ∧ 3 * p < 2 * n), Real.log p)) :=
      mul_le_mul_of_nonneg_left (le_trans hbig hmono) hc0
    have hstep1' : (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
        * (∑ b ∈ unitsMod m, (∑ p ∈ (Finset.range (n + 1)).filter
          (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
            ∧ 3 * p < 2 * n), Real.log p))
        - (δ / 8) * (m.totient : ℝ)
        ≤ ∑ b ∈ unitsMod m, Profiles408.halfProfile A z n δ m b := hstep2 ▸ hstep1
    linarith [hstep1', hmul]
  -- final numerical bound
  have hfac : (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
      * ((1 / 2 + δ / 2) * (1 - ε') * (((2 * n - 1) / 3 : ℕ) : ℝ) / 2)
      = ((1 / 2 + δ / 2) * (1 - ε') / 2)
        * ((3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
          * (((2 * n - 1) / 3 : ℕ) : ℝ)) := by ring
  have hlow : ((primorial z).totient : ℝ)
      * ((1 - κ) * (1 / 2 + δ / 2) * (1 - ε') / 2 - κ - δ / 8)
      ≤ ∑ b ∈ unitsMod m, Profiles408.halfProfile A z n δ m b := by
    have h1 : ((1 / 2 + δ / 2) * (1 - ε') / 2)
        * (((primorial z).totient : ℝ) * (1 - κ))
        ≤ ((1 / 2 + δ / 2) * (1 - ε') / 2)
          * ((3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
            * (((2 * n - 1) / 3 : ℕ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left hcard1
      have hε'le : ε' ≤ 1 := by linarith
      nlinarith
    have h2 : (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ))) * (Real.log 4 * z)
        ≤ ((primorial z).totient : ℝ) * κ := hcard2
    rw [← hfac] at h1
    have e1 : ((1 / 2 + δ / 2) * (1 - ε') / 2) * (((primorial z).totient : ℝ) * (1 - κ))
        = ((primorial z).totient : ℝ) * ((1 - κ) * (1 / 2 + δ / 2) * (1 - ε') / 2) := by ring
    have e2 : (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
        * ((1 / 2 + δ / 2) * (1 - ε') * (((2 * n - 1) / 3 : ℕ) : ℝ) / 2 - Real.log 4 * z)
        = (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ)))
            * ((1 / 2 + δ / 2) * (1 - ε') * (((2 * n - 1) / 3 : ℕ) : ℝ) / 2)
          - (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ))) * (Real.log 4 * z) := by ring
    have hmφ : (δ / 8) * (m.totient : ℝ) = (δ / 8) * ((primorial z).totient : ℝ) := by rw [htot]
    linarith [hmain, h1, h2, e1, e2, hmφ]
  have harith := mass_arith hδ hδsmall hε'0.le hε' hκ0 hκ
  have hφle : (0 : ℝ) ≤ ((primorial z).totient : ℝ) := hφpos.le
  rw [htot]
  have : ((primorial z).totient : ℝ) * (1 / 4) < ((primorial z).totient : ℝ)
      * ((1 - κ) * (1 / 2 + δ / 2) * (1 - ε') / 2 - κ - δ / 8) := by
    exact mul_lt_mul_of_pos_left harith hφpos
  have e3 : ((primorial z).totient : ℝ) * (1 / 4) = ((primorial z).totient : ℝ) / 4 := by ring
  linarith [hlow, this, e3]

private lemma log_four_le_two : Real.log 4 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 4)]
  have h1 : (2 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have h2 : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith

/-- The first threshold: the profile factor times the scale beats `φ (1 - κ)`. -/
private lemma card_bound_one (z n : ℕ) (hn : 1 ≤ n) {κ : ℝ} (hκn : 2 ≤ κ * n) :
    ((primorial z).totient : ℝ) * (1 - κ) ≤
      (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ))) * (((2 * n - 1) / 3 : ℕ) : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hφ : (0 : ℝ) ≤ ((primorial z).totient : ℝ) := Nat.cast_nonneg _
  have hY : 3 * (((2 * n - 1) / 3 : ℕ) : ℝ) ≥ 2 * (n : ℝ) - 4 := by
    have hdiv := Nat.div_add_mod (2 * n - 1) 3
    have hcast1 : ((3 * ((2 * n - 1) / 3) + (2 * n - 1) % 3 : ℕ) : ℝ)
        = ((2 * n - 1 : ℕ) : ℝ) := by exact_mod_cast hdiv
    have hcast2 : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
      have h0 : 0 < 2 * n := by omega
      push_cast [h0]; ring
    have hmod2 : (((2 * n - 1) % 3 : ℕ) : ℝ) ≤ 2 := by
      have := Nat.mod_lt (2 * n - 1) (by norm_num : 0 < 3)
      exact_mod_cast (by omega : (2 * n - 1) % 3 ≤ 2)
    push_cast at hcast1
    linarith
  have key : 1 - κ ≤ 3 * (((2 * n - 1) / 3 : ℕ) : ℝ) / (2 * (n : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  calc ((primorial z).totient : ℝ) * (1 - κ)
      ≤ ((primorial z).totient : ℝ)
          * (3 * (((2 * n - 1) / 3 : ℕ) : ℝ) / (2 * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left key hφ
    _ = (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ))) * (((2 * n - 1) / 3 : ℕ) : ℝ) := by
        ring

/-- The second threshold: the profile factor times `log 4 · z` is a `κ` error. -/
private lemma card_bound_two (z n : ℕ) (hn : 1 ≤ n) {κ : ℝ}
    (h : 3 * Real.log 4 * z ≤ 2 * κ * n) :
    (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ))) * (Real.log 4 * z)
      ≤ ((primorial z).totient : ℝ) * κ := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hφ : (0 : ℝ) ≤ ((primorial z).totient : ℝ) := Nat.cast_nonneg _
  have key : 3 * Real.log 4 * (z : ℝ) / (2 * (n : ℝ)) ≤ κ := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  calc (3 * ((primorial z).totient : ℝ) / (2 * (n : ℝ))) * (Real.log 4 * z)
      = ((primorial z).totient : ℝ) * (3 * Real.log 4 * (z : ℝ) / (2 * (n : ℝ))) := by ring
    _ ≤ ((primorial z).totient : ℝ) * κ := mul_le_mul_of_nonneg_left key hφ

/-- LEAF. Alsetri page 13, the profile definition and the display
sum f greater than phi of W divided by 4. The strict cutoff from Shao is
used here. Removing the possible endpoint changes the logarithmic sum by
at most log n, and the fixed density margin absorbs that error.
Only the explicit finite profile and its support are asserted. -/
theorem class_one_profile (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8)
    (z : ℕ) (hz : 3 ≤ z) (A : Set ℕ) (hA : A ⊆ P)
    (hsupport : ∀ a ∈ A, a % 3 = 1)
    (hdensity : 1 / 2 + δ ≤ lowerDensityRes A 1 3) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ m : ℕ, ∀ [NeZero m], m = primorial z / 2 →
      let f := Profiles408.halfProfile A z n δ m
      (∀ b, 0 ≤ f b ∧ f b ≤ 1) ∧ (∀ b, b.val % 3 ≠ 1 → f b = 0) ∧
      (m.totient : ℝ) / 4 < ∑ b ∈ unitsMod m, f b := by
  have hPa : ∀ p ∈ A, p.Prime := fun p hp => by
    simpa only [P, Set.mem_setOf_eq] using hA hp
  have hφpos : (0 : ℝ) < ((primorial z).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 (primorial_pos z)
  -- the relative error in the class sum
  set ε : ℝ := δ / (64 * (((primorial z).totient : ℝ) + 1)) with hεdef
  have hε0 : 0 < ε := by
    rw [hεdef]; positivity
  have hεφ : ε * ((primorial z).totient : ℝ) ≤ δ / 8 := by
    have hφ1 : (0 : ℝ) < ((primorial z).totient : ℝ) + 1 := by positivity
    have he : ε * ((primorial z).totient : ℝ)
        = δ * ((primorial z).totient : ℝ) / (64 * (((primorial z).totient : ℝ) + 1)) := by
      rw [hεdef]; ring
    rw [he, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨n₀, hn₀⟩ := LeanLab.HardyLittlewood1923.ap_sum_pow 0 (primorial z) (primorial_pos z) ε hε0
  have hn₀' : ∀ N : ℕ, n₀ ≤ N → ∀ a : ℕ, Nat.Coprime a (primorial z) →
      |(∑ p ∈ (Finset.range (N + 1)).filter
          (fun p => p.Prime ∧ p % primorial z = a % primorial z), Real.log p)
        - (N : ℝ) / ((primorial z).totient : ℝ)| ≤ ε * N := by
    intro N hN a ha
    have h := hn₀ N hN a ha
    simpa using h
  -- the density input at modulus `3`
  have hconv : ∀ X : ℕ, (∑ p ∈ (Finset.range (X + 1)).filter
        (fun p => p ∈ A ∧ p.Prime ∧ p % 3 = 1 % 3), Real.log p)
      = ∑ p ∈ (Finset.range (X + 1)).filter (fun p => p ∈ A), Real.log p := by
    intro X
    congr 1
    apply Finset.filter_congr
    intro p _
    constructor
    · rintro ⟨h1, -⟩; exact h1
    · intro h1
      refine ⟨h1, hPa p h1, ?_⟩
      have := hsupport p h1
      simpa using this
  obtain ⟨X₀, hX₀⟩ := LeanLab.DensityGoldbach.U1446.theta_A_lower A hA 3 1 (by norm_num)
    (by norm_num) (1 / 2 + δ / 2) (by linarith) (by linarith) (δ / 16) (by positivity)
    (by linarith)
  have hY₀ : ∀ X : ℕ, X₀ ≤ X →
      (1 / 2 + δ / 2) * (1 - δ / 16) * X / 2 ≤
        ∑ p ∈ (Finset.range (X + 1)).filter (fun p => p ∈ A), Real.log p := by
    intro X hX
    have h := hX₀ X hX
    rw [hconv X] at h
    have h2 : (3 : ℕ).totient = 2 := by decide
    have h3 : ((3 : ℕ).totient : ℝ) = ((2 : ℕ) : ℝ) := by rw [h2]
    simpa [h3] using h
  refine ⟨max (max (3 * n₀ + 10) (3 * X₀ + 10))
    (max (Nat.ceil (3 * ((primorial z).totient : ℝ) * z) + 1)
      (Nat.ceil (300 * (z : ℝ) / δ) + 1)), ?_⟩
  intro n hn m _ hm
  dsimp only
  have hna : 3 * n₀ + 10 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnb : 3 * X₀ + 10 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnc : Nat.ceil (3 * ((primorial z).totient : ℝ) * z) + 1 ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnd : Nat.ceil (300 * (z : ℝ) / δ) + 1 ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  -- the scale `Y = (2n-1)/3` is past every threshold
  have hnY : n₀ ≤ (2 * n - 1) / 3 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3)]
    omega
  have hXY : X₀ ≤ (2 * n - 1) / 3 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3)]
    omega
  -- the two thresholds for the mass comparison
  have hbig : 3 * ((primorial z).totient : ℝ) * z ≤ 2 * n := by
    have h1 : 3 * ((primorial z).totient : ℝ) * z ≤ (Nat.ceil (3 * ((primorial z).totient : ℝ) * z) : ℝ) :=
      Nat.le_ceil _
    have h2 : (Nat.ceil (3 * ((primorial z).totient : ℝ) * z) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (by omega : Nat.ceil (3 * ((primorial z).totient : ℝ) * z) ≤ n)
    linarith
  have hδn : 300 * (z : ℝ) ≤ δ * n := by
    have h1 : 300 * (z : ℝ) / δ ≤ (Nat.ceil (300 * (z : ℝ) / δ) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (300 * (z : ℝ) / δ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (by omega : Nat.ceil (300 * (z : ℝ) / δ) ≤ n)
    have h3 : 300 * (z : ℝ) / δ ≤ (n : ℝ) := le_trans h1 h2
    rw [div_le_iff₀ hδ] at h3
    linarith
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hκn : 2 ≤ (δ / 64) * (n : ℝ) := by nlinarith
  have hκ2 : 3 * Real.log 4 * (z : ℝ) ≤ 2 * (δ / 64) * (n : ℝ) := by
    have := log_four_le_two
    nlinarith
  have hcard1 := card_bound_one z n hn1 (κ := δ / 64) hκn
  have hcard2 := card_bound_two z n hn1 (κ := δ / 64) hκ2
  refine ⟨fun b => ⟨class_nonneg m b, ?_⟩, fun b hb => class_zero hδ hz hsupport m hm b hb, ?_⟩
  · exact class_le_one hδ hz hA ε hε0.le hεφ n₀ hn₀' m hm hn1 hnY hbig b
  · exact mass hδ hδsmall hz hA hsupport (δ / 16) (δ / 64) (by positivity) (by linarith)
      (by positivity) (by linarith) X₀ hY₀ m hm n hn1 hXY hcard1 hcard2

end

/-- Exact original Alsetri Theorem 1.1 statement.
CONDITIONAL ON the class profile and shared analytic supply leaves. -/
theorem alsetri_1_1_decomposed : Alsetri11 := by
  intro A hA hsupport hden
  let δ : ℝ := min ((lowerDensityRes A 1 3 - 1 / 2) / 2) (1 / 8)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδsmall : δ ≤ 1 / 8 := min_le_right _ _
  have hδden : 1 / 2 + δ ≤ lowerDensityRes A 1 3 := by
    have := min_le_left ((lowerDensityRes A 1 3 - 1 / 2) / 2) (1 / 8)
    linarith
  obtain ⟨z, hz, hLift⟩ := Decomp408b.weighted_lifting Decomp408a.alsetri_prop_4_1_decomposed
    Decomp408b.restriction_five_halves δ hδ
  obtain ⟨Np, hProfile⟩ := class_one_profile δ hδ hδsmall z hz A hA hsupport hδden
  obtain ⟨Nl, hNl⟩ := hLift z le_rfl A hA
  obtain ⟨hmpos, hmodd, hmsq, hm3⟩ := half_primorial_props hz
  let m := primorial z / 2
  have : NeZero m := ⟨hmpos.ne'⟩
  refine ⟨max Np Nl, ?_⟩
  intro n hn hnodd hn3
  obtain ⟨hbound, hsup, hmass⟩ := hProfile n (le_trans (le_max_left _ _) hn) m rfl
  let f := Profiles408.halfProfile A z n δ m
  have hx : (n : ZMod m).val % 3 = 0 := by
    rw [ZMod.val_natCast]
    have := (Nat.dvd_mod_iff hm3).mpr (Nat.dvd_of_mod_eq_zero hn3)
    exact Nat.mod_eq_zero_of_dvd this
  obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, he, h1, h2, h3, hs⟩ :=
    alsetri12_proved m hmodd hmsq hm3 f hbound hsup hmass (n : ZMod m) hx
  exact hNl n (le_trans (le_max_right _ _) hn) hnodd m rfl b₁ hb₁ b₂ hb₂ b₃ hb₃ he h1 h2 h3 hs

end LeanLab.DensityGoldbach.Decomp408d

#print axioms LeanLab.DensityGoldbach.Decomp408d.alsetri_1_1_decomposed
