import LeanLab.ExceptionalSet.UpJ200.Lemma2MV.Lemma55Split

/-!
# Proof of the leaf `lem55_pi12`, P0015 Lemma 5.5, the factor `Π₁ Π₂`, pages 360 and 361

Source P0015, Montgomery and Vaughan, The exceptional set in Goldbach's problem,
Acta Arith. 27, 1975, pages 360 and 361.

With `r₄ = [r₁, r₂]`, `r₅ = (r₄, |m|)` and `s = r₄/r₅`:
* `r₁ r₂ = (r₁, r₂) r₄ ≤ r₄²`, so `(r₁r₂r₄/r₅)^{1/2} ≤ r₄ s^{1/2}`;
* `φ(r₅) φ(s) ≤ φ(r₄)`, so the left side is at most `(r₅/φ(r₅)) · s^{3/2}/φ(s)²`;
* `r₅/φ(r₅) = ∏_{p | r₅} (1 - 1/p)⁻¹`, by `lem55_prod_combine`;
* `2 s³ ≤ 27 φ(s)⁴`, from `p³ ≤ (p-1)⁴` for `p ≥ 5`, the `Π₁ ≪ 1` step, so
  `s^{3/2}/φ(s)² ≤ 4`.

All sorry free. AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit

open Real Finset

/-- Helper for the `Π₁ ≪ 1` step, P0015 page 361: for `n` prime to 6, `n³ ≤ φ(n)⁴`,
since `p³ ≤ (p-1)⁴` for every prime `p ≥ 5`. -/
lemma pi12_coprime6 : ∀ n : ℕ, Nat.Coprime n 6 → n ^ 3 ≤ n.totient ^ 4 := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro hc
    have hp' : p.Prime := hp
    have h2 : ¬ p ∣ 6 := by
      intro hd
      have : p ∣ Nat.gcd (p ^ k) 6 := Nat.dvd_gcd (dvd_pow_self p hk.ne') hd
      rw [hc] at this
      exact hp'.one_lt.ne' (Nat.dvd_one.mp this)
    have h5 : 5 ≤ p := by
      have := hp'.two_le
      by_contra hlt
      interval_cases p <;> first | (simp_all; done) | exact absurd hp' (by decide)
    rw [Nat.totient_prime_pow hp' hk]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 4 := ⟨p - 4, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hb : (q + 4) ^ 3 ≤ (q + 3) ^ 4 := by nlinarith [sq_nonneg (q : ℕ), sq_nonneg (q * q)]
    have hj : (q + 4) ^ (3 * j) ≤ (q + 4) ^ (4 * j) := Nat.pow_le_pow_right (by omega) (by omega)
    calc ((q + 4) ^ (j + 1)) ^ 3 = (q + 4) ^ 3 * (q + 4) ^ (3 * j) := by ring
      _ ≤ (q + 3) ^ 4 * (q + 4) ^ (4 * j) := Nat.mul_le_mul hb hj
      _ = ((q + 4) ^ j * (q + 4 - 1)) ^ 4 := by
        rw [show q + 4 - 1 = q + 3 by omega]; ring
  | zero => intro _; simp
  | one => intro _; simp
  | coprime a b _ _ hab ha hb =>
    intro hc
    have hca : Nat.Coprime a 6 := Nat.Coprime.coprime_dvd_left (dvd_mul_right a b) hc
    have hcb : Nat.Coprime b 6 := Nat.Coprime.coprime_dvd_left (dvd_mul_left b a) hc
    rw [Nat.totient_mul hab, mul_pow, mul_pow]
    exact Nat.mul_le_mul (ha hca) (hb hcb)

/-- Helper for the `Π₁ ≪ 1` step, P0015 page 361: the prime 2 part. -/
lemma pi12_two_pow (a : ℕ) : (2 ^ a) ^ 3 ≤ 8 * (2 ^ a).totient ^ 4 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rw [Nat.totient_prime_pow Nat.prime_two ha]
  obtain ⟨j, rfl⟩ : ∃ j, a = j + 1 := ⟨a - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have : 2 ^ (3 * j) ≤ 2 ^ (4 * j) := Nat.pow_le_pow_right (by omega) (by omega)
  calc (2 ^ (j + 1)) ^ 3 = 8 * 2 ^ (3 * j) := by ring
    _ ≤ 8 * 2 ^ (4 * j) := Nat.mul_le_mul_left _ this
    _ = 8 * (2 ^ j * (2 - 1)) ^ 4 := by norm_num; ring

/-- Helper for the `Π₁ ≪ 1` step, P0015 page 361: the prime 3 part. -/
lemma pi12_three_pow (b : ℕ) : 16 * (3 ^ b) ^ 3 ≤ 27 * (3 ^ b).totient ^ 4 := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  rw [Nat.totient_prime_pow Nat.prime_three hb]
  obtain ⟨j, rfl⟩ : ∃ j, b = j + 1 := ⟨b - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have : 3 ^ (3 * j) ≤ 3 ^ (4 * j) := Nat.pow_le_pow_right (by omega) (by omega)
  calc 16 * (3 ^ (j + 1)) ^ 3 = 16 * 27 * 3 ^ (3 * j) := by ring
    _ ≤ 16 * 27 * 3 ^ (4 * j) := Nat.mul_le_mul_left _ this
    _ = 27 * (3 ^ j * (3 - 1)) ^ 4 := by norm_num; ring

/-- Arithmetic helper for `pi12_totient_pow4`: combining the three prime-power estimates. -/
lemma pi12_combine (x y z u v w : ℕ)
    (h : x ^ 3 * (16 * y ^ 3) * z ^ 3 ≤ 8 * u ^ 4 * (27 * v ^ 4) * w ^ 4) :
    2 * (x * (y * z)) ^ 3 ≤ 27 * (u * (v * w)) ^ 4 := by
  have e1 : 2 * (x * (y * z)) ^ 3 * 8 = x ^ 3 * (16 * y ^ 3) * z ^ 3 := by ring
  have e2 : 27 * (u * (v * w)) ^ 4 * 8 = 8 * u ^ 4 * (27 * v ^ 4) * w ^ 4 := by ring
  refine Nat.le_of_mul_le_mul_right (c := 8) ?_ (by norm_num)
  rw [e1, e2]; exact h

/-- P0015 Lemma 5.5 proof, the step `Π₁ ≪ 1` on page 361, in the form `2 n³ ≤ 27 φ(n)⁴`:
`φ(n)⁴/n³` is multiplicative, at least 1 at every prime power `p^k` with `p ≥ 5`, at least
`1/8` at powers of 2 and at least `16/27` at powers of 3. PROVED. -/
theorem pi12_totient_pow4 (n : ℕ) : 2 * n ^ 3 ≤ 27 * n.totient ^ 4 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨a, k, hk2, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 2 (by norm_num)
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk2
  obtain ⟨b, m, hm3, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0 3 (by norm_num)
  have hm2 : ¬ 2 ∣ m := fun h => hk2 (dvd_mul_of_dvd_right h _)
  have hm6 : Nat.Coprime m 6 := by
    have e6 : (6 : ℕ) = 2 * 3 := by norm_num
    rw [e6, Nat.coprime_mul_iff_right]
    exact ⟨(Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm2)),
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3))⟩
  have hc1 : Nat.Coprime (2 ^ a) (3 ^ b * m) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hk2)
  have hc2 : Nat.Coprime (3 ^ b) m :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3)
  rw [Nat.totient_mul hc1, Nat.totient_mul hc2]
  have h1 := pi12_two_pow a
  have h2 := pi12_three_pow b
  have h3 := pi12_coprime6 m hm6
  have := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  exact pi12_combine _ _ _ _ _ _ this

/-- P0015 page 361, `Π₂`: `r/φ(r) = ∏_{p | r} (1 - 1/p)⁻¹`, from `lem55_prod_combine`. -/
lemma pi12_euler (r : ℕ) (hr : 1 ≤ r) :
    (r : ℝ) / (r.totient : ℝ) = ∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ))⁻¹ := by
  have h := lem55_prod_combine r hr (r : ℤ) (by exact_mod_cast (by omega : r ≠ 0))
  simp only [Int.natAbs_natCast, Nat.gcd_self] at h
  have he : r.primeFactors.filter (fun p => ¬ p ∣ r) = ∅ :=
    Finset.filter_eq_empty_iff.mpr (fun p hp hnd => hnd (Nat.dvd_of_mem_primeFactors hp))
  rw [he, prod_empty, one_mul] at h
  exact h.symm

/-- P0015 Lemma 5.5 proof, the bound `Π₁ Π₂` of display (5.5), pages 360 and 361, PROVED. -/
theorem lem55_pi12_proof : ∃ C : ℝ, 0 < C ∧ ∀ (r₁ r₂ : ℕ), 1 ≤ r₁ → 1 ≤ r₂ → ∀ m : ℤ, m ≠ 0 →
    Real.sqrt ((r₁ : ℝ) * r₂ * (Nat.lcm r₁ r₂) / (Nat.gcd (Nat.lcm r₁ r₂) m.natAbs)) /
        (((Nat.lcm r₁ r₂).totient : ℝ) *
          ((Nat.lcm r₁ r₂ / Nat.gcd (Nat.lcm r₁ r₂) m.natAbs).totient : ℝ)) ≤
      C * ∏ p ∈ (Nat.gcd (Nat.lcm r₁ r₂) m.natAbs).primeFactors, (1 - 1 / (p : ℝ))⁻¹ := by
  refine ⟨4, by norm_num, ?_⟩
  intro r₁ r₂ hr₁ hr₂ m hm
  set r₄ := Nat.lcm r₁ r₂ with hr₄def
  set r₅ := Nat.gcd r₄ m.natAbs with hr₅def
  set s := r₄ / r₅ with hsdef
  have hr₄ : 1 ≤ r₄ := Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))
  have hr₅ : 1 ≤ r₅ := Nat.gcd_pos_of_pos_left _ hr₄
  have hdiv : r₅ ∣ r₄ := Nat.gcd_dvd_left _ _
  have hr₄eq : r₄ = r₅ * s := (Nat.mul_div_cancel' hdiv).symm
  have hs : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · rw [h] at hr₄eq; omega
    · exact h
  have hgl : Nat.gcd r₁ r₂ ≤ r₄ :=
    Nat.le_of_dvd hr₄ (dvd_trans (Nat.gcd_dvd_left _ _) (Nat.dvd_lcm_left _ _))
  have hprodN : r₁ * r₂ ≤ r₄ * r₄ := by
    rw [← Nat.gcd_mul_lcm r₁ r₂]; exact Nat.mul_le_mul_right _ hgl
  have hsup : r₅.totient * s.totient ≤ r₄.totient := by
    rw [hr₄eq]; exact Nat.totient_super_multiplicative _ _
  have hφ5 : 0 < r₅.totient := Nat.totient_pos.mpr hr₅
  have hφs : 0 < s.totient := Nat.totient_pos.mpr hs
  have hkey := pi12_totient_pow4 s
  -- real casts
  have R4 : (r₄ : ℝ) = r₅ * s := by exact_mod_cast hr₄eq
  have R5 : (0 : ℝ) < r₅ := by exact_mod_cast hr₅
  have RS : (0 : ℝ) < s := by exact_mod_cast hs
  have F5 : (0 : ℝ) < r₅.totient := by exact_mod_cast hφ5
  have FS : (0 : ℝ) < s.totient := by exact_mod_cast hφs
  have F4 : (r₅.totient : ℝ) * s.totient ≤ r₄.totient := by exact_mod_cast hsup
  have P12 : (r₁ : ℝ) * r₂ ≤ r₄ * r₄ := by exact_mod_cast hprodN
  have KEY : (2 : ℝ) * s ^ 3 ≤ 27 * (s.totient : ℝ) ^ 4 := by exact_mod_cast hkey
  rw [← pi12_euler r₅ hr₅]
  -- the numerator
  have hnum : Real.sqrt ((r₁ : ℝ) * r₂ * r₄ / r₅) ≤ r₄ * Real.sqrt s := by
    rw [show (r₄ : ℝ) * Real.sqrt s = Real.sqrt ((r₄ : ℝ) ^ 2 * s) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ R5]
    calc (r₁ : ℝ) * r₂ * r₄ ≤ r₄ * r₄ * r₄ := by
          exact mul_le_mul_of_nonneg_right P12 (by positivity)
      _ = (r₄ : ℝ) ^ 2 * s * r₅ := by rw [R4]; ring
  -- the factor s^{3/2}/φ(s)² ≤ 4
  have hsq : Real.sqrt s * s ≤ 4 * (s.totient : ℝ) ^ 2 := by
    have h0 : 0 ≤ Real.sqrt s * s := by positivity
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 4 * (s.totient : ℝ) ^ 2)]
    rw [← Real.sqrt_sq h0]
    apply Real.sqrt_le_sqrt
    rw [mul_pow, Real.sq_sqrt RS.le]
    nlinarith [KEY, pow_pos FS 4]
  have hden : (r₅.totient : ℝ) * s.totient * s.totient ≤ r₄.totient * s.totient :=
    mul_le_mul_of_nonneg_right F4 FS.le
  have hdpos : (0 : ℝ) < r₅.totient * s.totient * s.totient := by positivity
  calc Real.sqrt ((r₁ : ℝ) * r₂ * r₄ / r₅) / ((r₄.totient : ℝ) * s.totient)
      ≤ (r₄ * Real.sqrt s) / ((r₅.totient : ℝ) * s.totient * s.totient) :=
        div_le_div₀ (by positivity) hnum hdpos hden
    _ = (r₅ : ℝ) / r₅.totient * ((Real.sqrt s * s) / (s.totient : ℝ) ^ 2) := by
        rw [R4]; field_simp
    _ ≤ (r₅ : ℝ) / r₅.totient * 4 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_iff₀ (by positivity)]; exact hsq
    _ = 4 * ((r₅ : ℝ) / r₅.totient) := by ring

/-- Exact-type twin of the leaf `lem55_pi12`. -/
theorem lem55_pi12_twin : type_of% @lem55_pi12 := lem55_pi12_proof

end LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit

#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.lem55_pi12_twin
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.pi12_totient_pow4
