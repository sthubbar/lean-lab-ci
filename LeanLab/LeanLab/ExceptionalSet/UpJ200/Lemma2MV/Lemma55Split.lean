import LeanLab.ExceptionalSet.UpJ200.Lemma2MV.Remainder66Split

/-!
# Split of the leaf `rem66_lemma55`, P0015 Lemma 5.5, display (5.4), pages 360 and 361

Source P0015, Montgomery and Vaughan, The exceptional set in Goldbach's problem,
Acta Arith. 27, 1975, read from the page image of `papers/P0015.pdf`, pages 360 and 361.

Notation of the proof on page 360: `r₄ = [r₁, r₂]`, `r₅ = (r₄, m)`, `q = r₄ k`.
* LEAF `lem55_termwise`, HARD: display (5.5) termwise. From Lemmas 5.1, 5.2, 5.4, the
  term of `q = r₄ k` vanishes unless `(k, r₄) = 1` and `μ(k)² = 1`, and is at most
  `(r₁r₂r₄/r₅)^{1/2} φ(r₄)⁻¹ φ(r₄/r₅)⁻¹ μ(k)² φ(k)⁻¹ φ(k/(k,m))⁻¹`, up to an absolute constant.
* LEAF `lem55_ksum`, MEDIUM: the Euler product bound of page 360, the `k` sum is
  `≪ ∏_{p | m, p ∤ r₄} (1 - 1/p)⁻¹`.
* LEAF `lem55_pi12`, MEDIUM: the other factor of (5.5) is `Π₁ Π₂` with `Π₁ ≪ 1` and
  `Π₂ ≤ ∏_{p | r₅} (1 - 1/p)⁻¹`, pages 360 and 361.
* `lem55_prod_combine`, PROVED: the two Euler products combine to `|m|/φ(|m|)`,
  "we combine these three estimates", page 361.
* `lemma55_of_leaves`, PROVED sorry free from the four steps: the exact statement of
  `rem66_lemma55`, checked by a twin typed `type_of% @rem66_lemma55`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit

open Real Finset

open DirichletCharacter in
/-- LEAF: P0015 Lemma 5.5 proof, display (5.5), page 360, termwise, via Lemmas 5.1, 5.2, 5.4,
class HARD. With `r₄ = [r₁, r₂]`, `r₅ = (r₄, |m|)` and `q = r₄ k`, the term of `q` in (5.4) is
at most an absolute constant times
`(r₁r₂r₄/r₅)^{1/2} φ(r₄)⁻¹ φ(r₄/r₅)⁻¹ · μ(k)² [(k, r₄) = 1] φ(k)⁻¹ φ(k/(k,m))⁻¹`. -/
theorem lem55_termwise : ∃ C : ℝ, 0 < C ∧ ∀ (r₁ r₂ : ℕ) (ψ₁ : DirichletCharacter ℂ r₁)
    (ψ₂ : DirichletCharacter ℂ r₂), 1 ≤ r₁ → 1 ≤ r₂ → ψ₁.IsPrimitive → ψ₂.IsPrimitive →
    ∀ m : ℤ, m ≠ 0 → ∀ q : ℕ, 1 ≤ q → ∀ h : r₁ ∣ q ∧ r₂ ∣ q,
      ‖rem66_cchi (changeLevel h.1 ψ₁ * changeLevel h.2 ψ₂) m *
          rem66_cchi (changeLevel h.1 ψ₁)⁻¹ 1 * rem66_cchi (changeLevel h.2 ψ₂)⁻¹ 1‖ /
          (q.totient : ℝ) ^ 2 ≤
        C * (Real.sqrt ((r₁ : ℝ) * r₂ * (Nat.lcm r₁ r₂) / (Nat.gcd (Nat.lcm r₁ r₂) m.natAbs)) /
            (((Nat.lcm r₁ r₂).totient : ℝ) *
              ((Nat.lcm r₁ r₂ / Nat.gcd (Nat.lcm r₁ r₂) m.natAbs).totient : ℝ))) *
          (if Nat.Coprime (q / Nat.lcm r₁ r₂) (Nat.lcm r₁ r₂) ∧ Squarefree (q / Nat.lcm r₁ r₂) then
            1 / (((q / Nat.lcm r₁ r₂).totient : ℝ) *
              (((q / Nat.lcm r₁ r₂) / Nat.gcd (q / Nat.lcm r₁ r₂) m.natAbs).totient : ℝ))
          else 0) := by
  sorry

/-- LEAF: P0015 Lemma 5.5 proof, the Euler product bound after display (5.5), page 360, class
MEDIUM. The sum over `k = q/r₄` with `(k, r₄) = 1` of `μ(k)² φ(k)⁻¹ φ(k/(k,m))⁻¹` equals
`∏_{p ∤ r₄m} (1 + (p-1)⁻²) ∏_{p | m, p ∤ r₄} (1 + (p-1)⁻¹) ≪ ∏_{p | m, p ∤ r₄} (1 - 1/p)⁻¹`;
here truncated to `q ≤ N` and written over `q = r₄ k`. -/
theorem lem55_ksum : ∃ C : ℝ, 0 < C ∧ ∀ (r₄ : ℕ), 1 ≤ r₄ → ∀ m : ℤ, m ≠ 0 → ∀ N : ℕ,
    ∑ q ∈ Icc 1 N, (if r₄ ∣ q then
        (if Nat.Coprime (q / r₄) r₄ ∧ Squarefree (q / r₄) then
          1 / (((q / r₄).totient : ℝ) * (((q / r₄) / Nat.gcd (q / r₄) m.natAbs).totient : ℝ))
        else 0) else 0) ≤
      C * ∏ p ∈ m.natAbs.primeFactors.filter (fun p => ¬ p ∣ r₄), (1 - 1 / (p : ℝ))⁻¹ := by
  sorry

/-- LEAF: P0015 Lemma 5.5 proof, the bound `Π₁ Π₂` of the other factor of display (5.5),
pages 360 and 361, class MEDIUM. With `r₄ = [r₁, r₂]` and `r₅ = (r₄, |m|)`,
`(r₁r₂r₄/r₅)^{1/2} φ(r₄)⁻¹ φ(r₄/r₅)⁻¹ = Π₁ Π₂` with `Π₁ ≪ 1` and
`Π₂ ≤ ∏_{p | r₅} (1 - 1/p)⁻¹`. -/
theorem lem55_pi12 : ∃ C : ℝ, 0 < C ∧ ∀ (r₁ r₂ : ℕ), 1 ≤ r₁ → 1 ≤ r₂ → ∀ m : ℤ, m ≠ 0 →
    Real.sqrt ((r₁ : ℝ) * r₂ * (Nat.lcm r₁ r₂) / (Nat.gcd (Nat.lcm r₁ r₂) m.natAbs)) /
        (((Nat.lcm r₁ r₂).totient : ℝ) *
          ((Nat.lcm r₁ r₂ / Nat.gcd (Nat.lcm r₁ r₂) m.natAbs).totient : ℝ)) ≤
      C * ∏ p ∈ (Nat.gcd (Nat.lcm r₁ r₂) m.natAbs).primeFactors, (1 - 1 / (p : ℝ))⁻¹ := by
  sorry

/-- P0015 Lemma 5.5 proof, page 361, "we combine these three estimates", PROVED.
With `r₅ = (r₄, |m|)`, `∏_{p | m, p ∤ r₄} (1 - 1/p)⁻¹ ∏_{p | r₅} (1 - 1/p)⁻¹ = |m|/φ(|m|)`. -/
theorem lem55_prod_combine : ∀ (r₄ : ℕ), 1 ≤ r₄ → ∀ m : ℤ, m ≠ 0 →
    (∏ p ∈ m.natAbs.primeFactors.filter (fun p => ¬ p ∣ r₄), (1 - 1 / (p : ℝ))⁻¹) *
        (∏ p ∈ (Nat.gcd r₄ m.natAbs).primeFactors, (1 - 1 / (p : ℝ))⁻¹) =
      (m.natAbs : ℝ) / (m.natAbs.totient : ℝ) := by
  classical
  intro r₄ hr₄ m hm
  set n := m.natAbs with hn'
  have hn : n ≠ 0 := Int.natAbs_ne_zero.mpr hm
  have hr : r₄ ≠ 0 := by omega
  have hset : (Nat.gcd r₄ n).primeFactors = n.primeFactors.filter (fun p => p ∣ r₄) := by
    rw [Nat.primeFactors_gcd hr hn]
    ext p
    simp only [mem_inter, mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩
      exact ⟨⟨h4, h5, h6⟩, h2⟩
    · rintro ⟨⟨h4, h5, h6⟩, h2⟩
      exact ⟨⟨h4, h2, hr⟩, h4, h5, h6⟩
  rw [hset, mul_comm, prod_filter_mul_prod_filter_not]
  have hq := Nat.totient_eq_mul_prod_factors n
  have hR : (n.totient : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have := congrArg (Rat.cast : ℚ → ℝ) hq
    push_cast at this
    exact this
  have hprod : ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) ≠ 0 := by
    refine prod_ne_zero_iff.mpr (fun p hp => ?_)
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    exact ne_of_gt (by linarith)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [hR]
  simp only [one_div]
  rw [prod_inv_distrib]
  field_simp

lemma lem55_euler_nonneg (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    0 ≤ ∏ p ∈ s, (1 - 1 / (p : ℝ))⁻¹ := by
  refine prod_nonneg (fun p hp => inv_nonneg.mpr ?_)
  have h1 : (1 : ℝ) ≤ p := by exact_mod_cast (hs p hp).one_lt.le
  rw [sub_nonneg, div_le_one (by linarith)]
  exact h1

open DirichletCharacter in
/-- P0015 Lemma 5.5, display (5.4), page 360: the exact statement of `rem66_lemma55`, PROVED
sorry free from the four leaves of its proof on pages 360 and 361. -/
theorem lemma55_of_leaves (H1 : type_of% @lem55_termwise) (H2 : type_of% @lem55_ksum)
    (H3 : type_of% @lem55_pi12) (H4 : type_of% @lem55_prod_combine) :
    type_of% @rem66_lemma55 := by
  classical
  obtain ⟨C1, hC1, h1⟩ := H1
  obtain ⟨C2, hC2, h2⟩ := H2
  obtain ⟨C3, hC3, h3⟩ := H3
  refine ⟨C1 * C2 * C3, by positivity, ?_⟩
  intro r₁ r₂ ψ₁ ψ₂ hp₁ hp₂ m hm N
  have hρ : 0 ≤ C1 * C2 * C3 * ((m.natAbs : ℝ) / (m.natAbs.totient : ℝ)) := by positivity
  rcases Nat.eq_zero_or_pos r₁ with hr₁ | hr₁
  · refine le_trans (le_of_eq (sum_eq_zero fun q hq => dif_neg ?_)) hρ
    rintro ⟨h, -⟩
    have := (mem_Icc.mp hq).1
    rw [hr₁, zero_dvd_iff] at h
    omega
  rcases Nat.eq_zero_or_pos r₂ with hr₂ | hr₂
  · refine le_trans (le_of_eq (sum_eq_zero fun q hq => dif_neg ?_)) hρ
    rintro ⟨-, h⟩
    have := (mem_Icc.mp hq).1
    rw [hr₂, zero_dvd_iff] at h
    omega
  set r₄ := Nat.lcm r₁ r₂ with hr₄
  have hr₄1 : 1 ≤ r₄ := Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))
  set A := Real.sqrt ((r₁ : ℝ) * r₂ * r₄ / (Nat.gcd r₄ m.natAbs)) /
    ((r₄.totient : ℝ) * ((r₄ / Nat.gcd r₄ m.natAbs).totient : ℝ)) with hA
  have hA0 : 0 ≤ A := by positivity
  set g : ℕ → ℝ := fun q => if r₄ ∣ q then
      (if Nat.Coprime (q / r₄) r₄ ∧ Squarefree (q / r₄) then
        1 / (((q / r₄).totient : ℝ) * (((q / r₄) / Nat.gcd (q / r₄) m.natAbs).totient : ℝ))
      else 0) else 0 with hg
  set P1 := ∏ p ∈ m.natAbs.primeFactors.filter (fun p => ¬ p ∣ r₄), (1 - 1 / (p : ℝ))⁻¹
  set P2 := ∏ p ∈ (Nat.gcd r₄ m.natAbs).primeFactors, (1 - 1 / (p : ℝ))⁻¹
  have hP1 : 0 ≤ P1 := lem55_euler_nonneg _ (fun p hp =>
    Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)
  have hP2 : 0 ≤ P2 := lem55_euler_nonneg _ (fun p hp => Nat.prime_of_mem_primeFactors hp)
  calc ∑ q ∈ Icc 1 N, (if h : r₁ ∣ q ∧ r₂ ∣ q then
        ‖rem66_cchi (changeLevel h.1 ψ₁ * changeLevel h.2 ψ₂) m *
          rem66_cchi (changeLevel h.1 ψ₁)⁻¹ 1 * rem66_cchi (changeLevel h.2 ψ₂)⁻¹ 1‖ /
          (q.totient : ℝ) ^ 2
      else 0)
        ≤ ∑ q ∈ Icc 1 N, C1 * A * g q := by
          refine sum_le_sum (fun q hq => ?_)
          have hq1 := (mem_Icc.mp hq).1
          by_cases h : r₁ ∣ q ∧ r₂ ∣ q
          · rw [dif_pos h]
            have hd : r₄ ∣ q := Nat.lcm_dvd h.1 h.2
            have := h1 r₁ r₂ ψ₁ ψ₂ hr₁ hr₂ hp₁ hp₂ m hm q hq1 h
            simp only [hg, if_pos hd]
            exact this
          · rw [dif_neg h]
            have : 0 ≤ g q := by
              simp only [hg]
              split_ifs <;> positivity
            positivity
    _ = C1 * A * ∑ q ∈ Icc 1 N, g q := by rw [mul_sum]
    _ ≤ C1 * A * (C2 * P1) := mul_le_mul_of_nonneg_left (h2 r₄ hr₄1 m hm N) (by positivity)
    _ ≤ C1 * (C3 * P2) * (C2 * P1) := by
          gcongr
          exact h3 r₁ r₂ hr₁ hr₂ m hm
    _ = C1 * C2 * C3 * (P1 * P2) := by ring
    _ = C1 * C2 * C3 * ((m.natAbs : ℝ) / (m.natAbs.totient : ℝ)) := by
          rw [H4 r₄ hr₄1 m hm]

/-- The exact statement of `rem66_lemma55`, CONDITIONAL ON the four leaves above. -/
theorem lemma55_split : type_of% @rem66_lemma55 :=
  lemma55_of_leaves lem55_termwise lem55_ksum lem55_pi12 lem55_prod_combine

/-- Twin check: `lemma55_split` has exactly the type of `rem66_lemma55`. -/
theorem lemma55_split_twin : type_of% @rem66_lemma55 := lemma55_split

end LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit

#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.lemma55_of_leaves
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.lemma55_split
