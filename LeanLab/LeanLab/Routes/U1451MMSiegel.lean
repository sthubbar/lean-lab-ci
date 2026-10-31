import Mathlib
import LeanLab.Routes.U1449Siegel

/-!
# R-0047, T2 FRONTIER salvage: Matomaki-Merikoski 2022, Theorem 1.4, as a named Prop,
# and the vanishing of its main term at multiples of a prime exceptional modulus q ≡ 3 mod 4

Unit U-1451, cloud run 20261022T0003Z-15508. AI wrote this Lean code, Claude. Checked only by
the Lean kernel. Binary Goldbach is OPEN; nothing here is progress on it.

Source: K. Matomäki, J. Merikoski, "Siegel zeros, twin primes, Goldbach's conjecture, and
primes in short intervals", arXiv 2112.11412 v2, 5 Feb 2022, Section 1, Theorem 1.4.

`MM14` states Theorem 1.4 with the paper's own normalisation. `mainTerm_eq_zero` is the
unconditional arithmetic fact that its main term `h 𝔖_h (1 + χ(-1) M_h)` is `0` when `q` is
a prime `≡ 3 mod 4` dividing `h`; `chi_neg_one` derives `χ(-1) = -1` for every nontrivial
quadratic character mod such `q` from U-1449's `neg_flip`, and `one_add_legendre_neg_one`
derives the same identity for the Legendre symbol from U-1449's `pair_weight_zero`.
`goldbach_small_of_MM14` is CONDITIONAL ON `MM14`: at such `h` the Goldbach sum is bounded by
the error term alone.

Vacuity caveat. The Siegel zero hypothesis of `MM14` is expected to be false for every `q`;
no instance of it is known. The vacuity examples below instantiate every other hypothesis.
-/

namespace LeanLab.Routes.U1451

open Real ArithmeticFunction Finset

/-- The twin prime constant factor `∏_{p > 2} (1 - 1/(p - 1)^2)`. -/
noncomputable def twinProd : ℝ :=
  ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p.1 : ℝ) - 1) ^ 2)

/-- The singular series of MM 2022, display after (2):
`𝔖_h = 1_{2 ∣ h} · 2 ∏_{p > 2} (1 - 1/(p-1)^2) ∏_{p ∣ h, p > 2} (1 + 1/(p - 2))`. -/
noncomputable def singSeries (h : ℕ) : ℝ :=
  if 2 ∣ h then 2 * twinProd * ∏ p ∈ h.primeFactors.filter (fun p => 2 < p), (1 + 1 / ((p : ℝ) - 2))
  else 0

/-- The correction of MM 2022 Theorems 1.3, 1.4, with `q = 2^r q'`, `q'` odd:
`M_h = 1_{φ(2^r) ∣ h} (-1)^{h/φ(2^r)} ∏_{p ∣ q', p ∤ h} (-1/(p - 2))`. -/
noncomputable def corr (q h : ℕ) : ℝ :=
  let r := q.factorization 2
  let q' := q / 2 ^ r
  if Nat.totient (2 ^ r) ∣ h then
    (-1 : ℝ) ^ (h / Nat.totient (2 ^ r)) *
      ∏ p ∈ q'.primeFactors.filter (fun p => ¬ p ∣ h), (-1 / ((p : ℝ) - 2))
  else 0

/-- The Goldbach sum `∑_{n₁ + n₂ = h, n₁, n₂ ≤ h} Λ(n₁) Λ(n₂)`; `Λ 0 = 0`. -/
noncomputable def goldbachSum (h : ℕ) : ℝ :=
  ∑ n ∈ range (h + 1), (Λ n : ℝ) * Λ (h - n)

/-- The main term `h 𝔖_h (1 + χ(-1) M_h)` of MM 2022 Theorem 1.4. -/
noncomputable def mainTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (h : ℕ) : ℂ :=
  (h : ℂ) * (singSeries h : ℂ) * (1 + χ (-1) * (corr q h : ℂ))

/-- The error bracket of MM 2022 Theorem 1.4, `V = log h / log q`:
`(h/φ(h)) h (exp(-C √(V log η)) + exp(-C (log h)^{3/5 - ε}) + V (log η)^6 / η)`. -/
noncomputable def errTerm (C ε η : ℝ) (q h : ℕ) : ℝ :=
  let V := Real.log h / Real.log q
  (h / (Nat.totient h : ℝ)) * h *
    (Real.exp (-C * Real.sqrt (V * Real.log η)) + Real.exp (-C * (Real.log h) ^ (3 / 5 - ε))
      + V * (Real.log η) ^ 6 / η)

/-- **Matomäki-Merikoski 2022, Theorem 1.4**, arXiv 2112.11412, as a named hypothesis.
For `C ≥ 1`, `ε > 0` there is `K` such that for every primitive quadratic character `χ`
mod `q ≥ 2` whose L-function has the real zero `β₀ = 1 - 1/(η log q)`, `η ≥ 10`, and every
integer `h ≥ q^10`, the Goldbach sum equals `h 𝔖_h (1 + χ(-1) M_h)` up to `K` times the error
bracket. `χ ≠ 1` is implied by primitivity at `q ≥ 2` and is kept explicit. -/
def MM14 : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (η : ℝ) (h : ℕ),
    2 ≤ q → χ.IsPrimitive → χ.IsQuadratic → χ ≠ 1 → 10 ≤ η →
    DirichletCharacter.LFunction χ ((1 - 1 / (η * Real.log q) : ℝ) : ℂ) = 0 →
    (q : ℝ) ^ 10 ≤ h →
    ‖(goldbachSum h : ℂ) - mainTerm χ h‖ ≤ K * errTerm C ε η q h

/-- Derived from U-1449 `pair_weight_zero`: for `p ≡ 3 mod 4`, `1 + (-1/p) = 0`.
Take a non-residue `a`; the pair weight `(1 - χ(a))(1 - χ(-a)) = 2 (1 - χ(-a))` vanishes. -/
theorem one_add_legendre_neg_one (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3) :
    1 + legendreSym p (-1) = 0 := by
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp4
  have hc : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  obtain ⟨b, hb⟩ := FiniteField.exists_nonsquare hc
  have hb0 : b ≠ 0 := by rintro rfl; exact hb ⟨0, by simp⟩
  set a : ℤ := (b.val : ℤ)
  have hab : ((a : ℤ) : ZMod p) = b := by simp [a]
  have ha0 : ((a : ℤ) : ZMod p) ≠ 0 := by rw [hab]; exact hb0
  have hla : legendreSym p a = -1 := by
    rw [legendreSym.eq_neg_one_iff, hab]; exact hb
  have hw := LeanLab.Routes.U1449.pair_weight_zero p hp4 ha0
  have hneg : legendreSym p (-a) = legendreSym p (-1) * legendreSym p a := by
    rw [← legendreSym.mul]; ring_nf
  rw [hla, hneg, hla] at hw
  linarith

/-- Every unit mod a prime `p ≡ 3 mod 4` is a square or minus a square. -/
theorem sq_or_neg_sq (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3) {u : ZMod p} (hu : u ≠ 0) :
    IsSquare u ∨ IsSquare (-u) := by
  set a : ℤ := (u.val : ℤ)
  have hau : ((a : ℤ) : ZMod p) = u := by simp [a]
  have ha0 : ((a : ℤ) : ZMod p) ≠ 0 := by rw [hau]; exact hu
  rcases legendreSym.eq_one_or_neg_one p ha0 with h | h
  · left; rw [← hau]; exact (legendreSym.eq_one_iff p ha0).mp h
  · right
    have h' : legendreSym p (-a) = 1 := by
      rw [LeanLab.Routes.U1449.neg_flip p hp4, h]; norm_num
    have hn0 : ((-a : ℤ) : ZMod p) ≠ 0 := by push_cast; exact neg_ne_zero.mpr ha0
    have := (legendreSym.eq_one_iff p hn0).mp h'
    rw [← hau]; push_cast at this; exact this

/-- For a quadratic `χ` and a square `u`, `χ(u) ∈ {0, 1}`, and `= 1` when `u` is a unit. -/
theorem chi_sq {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ.IsQuadratic) (w : ZMod q) :
    χ (w * w) = 0 ∨ χ (w * w) = 1 := by
  rw [map_mul]
  rcases hχ w with h | h | h <;> rw [h] <;> norm_num

/-- `χ(-1) = -1` for every nontrivial quadratic Dirichlet character mod a prime `q ≡ 3 mod 4`. -/
theorem chi_neg_one (q : ℕ) [Fact q.Prime] (hq4 : q % 4 = 3) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) (h1 : χ ≠ 1) : χ (-1) = -1 := by
  have hm1 : IsUnit (-1 : ZMod q) := isUnit_one.neg
  have hne0 : χ (-1) ≠ 0 := (hm1.map χ).ne_zero
  rcases hχ (-1) with h | h | h
  · exact absurd h hne0
  · exfalso; apply h1
    apply MulChar.ext
    intro u
    rw [MulChar.one_apply_coe]
    have hu0 : (u : ZMod q) ≠ 0 := u.ne_zero
    have hχu : χ u ≠ 0 := (u.isUnit.map χ).ne_zero
    rcases sq_or_neg_sq q hq4 hu0 with ⟨w, hw⟩ | ⟨w, hw⟩
    · rw [hw]; rcases chi_sq hχ w with h' | h'
      · rw [← hw] at h'; exact absurd h' hχu
      · exact h'
    · have : (u : ZMod q) = (-1) * (w * w) := by rw [← hw]; ring
      have hww : χ (w * w) ≠ 0 := by
        intro h0; apply hχu; rw [this, map_mul, h0, mul_zero]
      rw [this, map_mul, h, one_mul]
      rcases chi_sq hχ w with h' | h'
      · exact absurd h' hww
      · exact h'
  · exact h

/-- `M_h = (-1)^h` when `q` is an odd prime dividing `h`. -/
theorem corr_of_dvd (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) {h : ℕ} (hqh : q ∣ h) :
    corr q h = (-1 : ℝ) ^ h := by
  have hr : q.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h2 => hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h2).symm)
  have hfil : (q.primeFactors.filter (fun p => ¬ p ∣ h)) = ∅ := by
    rw [hq.primeFactors, Finset.filter_eq_empty_iff]
    intro p hp; rw [Finset.mem_singleton] at hp; subst hp; simpa using hqh
  simp [corr, hr, hfil]

/-- **Main term vanishing**, unconditional: for `q` a prime `≡ 3 mod 4`, `χ` a nontrivial
quadratic character mod `q`, and `q ∣ h`, the MM 2022 Theorem 1.4 main term is `0`. -/
theorem mainTerm_eq_zero (q : ℕ) [Fact q.Prime] (hq4 : q % 4 = 3) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) (h1 : χ ≠ 1) {h : ℕ} (hqh : q ∣ h) : mainTerm χ h = 0 := by
  have hq2 : q ≠ 2 := by rintro rfl; norm_num at hq4
  unfold mainTerm
  rw [corr_of_dvd q Fact.out hq2 hqh, chi_neg_one q hq4 χ hχ h1]
  by_cases he : 2 ∣ h
  · obtain ⟨k, rfl⟩ := he
    simp [pow_mul]
  · simp [singSeries, he]

/-- **CONDITIONAL ON `MM14`**: in the Siegel world with exceptional prime modulus
`q ≡ 3 mod 4`, the Goldbach sum at every `h ≥ q^10` divisible by `q` is at most the MM error
term; the main term contributes nothing. -/
theorem goldbach_small_of_MM14 (hMM : MM14) (C : ℝ) (hC : 1 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, ∀ (q : ℕ) [Fact q.Prime] [NeZero q] (χ : DirichletCharacter ℂ q) (η : ℝ) (h : ℕ),
      q % 4 = 3 → χ.IsPrimitive → χ.IsQuadratic → χ ≠ 1 → 10 ≤ η →
      DirichletCharacter.LFunction χ ((1 - 1 / (η * Real.log q) : ℝ) : ℂ) = 0 →
      (q : ℝ) ^ 10 ≤ h → q ∣ h →
      |goldbachSum h| ≤ K * errTerm C ε η q h := by
  obtain ⟨K, hK⟩ := hMM C hC ε hε
  refine ⟨K, fun q _ _ χ η h hq4 hp hχ h1 hη hL hh hqh => ?_⟩
  have h2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  have := hK q χ η h h2 hp hχ h1 hη hL hh
  rw [mainTerm_eq_zero q hq4 χ hχ h1 hqh, sub_zero, Complex.norm_real, Real.norm_eq_abs] at this
  exact this

/-! ## Vacuity -/

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The Legendre character mod `7` as a Dirichlet character over `ℂ`. -/
noncomputable def chi7 : DirichletCharacter ℂ 7 :=
  (quadraticChar (ZMod 7)).ringHomComp (Int.castRingHom ℂ)

/-- Vacuity: `chi7` is quadratic and nontrivial, `7 ≡ 3 mod 4`, `7 ∣ 2·7^10`, `7^10 ≤ 2·7^10`,
so every hypothesis of `mainTerm_eq_zero` holds; and its conclusion is not a typo: there
`χ(-1) = -1` and `M_h = 1`. The Siegel zero hypothesis of `MM14` has no known instance. -/
theorem vacuity_chi7 : chi7.IsQuadratic ∧ chi7 ≠ 1 ∧ 7 % 4 = 3 ∧ 7 ∣ 2 * 7 ^ 10 ∧
    ((7 : ℕ) : ℝ) ^ 10 ≤ ((2 * 7 ^ 10 : ℕ) : ℝ) ∧ chi7 (-1) = -1 ∧ corr 7 (2 * 7 ^ 10) = 1 := by
  have hq : chi7.IsQuadratic := (quadraticChar_isQuadratic (ZMod 7)).comp _
  have hne : chi7 ≠ 1 := by
    intro h
    have h3 : chi7 3 = 1 := by
      rw [h]; exact MulChar.one_apply (isUnit_iff_ne_zero.mpr (by decide))
    have : quadraticChar (ZMod 7) 3 = -1 := by
      rw [quadraticChar_neg_one_iff_not_isSquare]; decide
    simp [chi7, MulChar.ringHomComp_apply, this] at h3
    norm_num at h3
  refine ⟨hq, hne, by norm_num, ⟨2 * 7 ^ 9, by ring⟩, by push_cast; nlinarith [pow_pos (by norm_num : (0:ℝ) < 7) 10], chi_neg_one 7 (by norm_num) chi7 hq hne, ?_⟩
  rw [corr_of_dvd 7 (by norm_num) (by norm_num) ⟨2 * 7 ^ 9, by ring⟩]
  rw [pow_mul]; norm_num

/-- The vanishing really needs `q ≡ 3 mod 4`: the Legendre symbol mod 5 has `1 + (-1/5) = 2`. -/
theorem flip_needed5 : 1 + legendreSym 5 (-1) = 2 := by
  have : legendreSym 5 (-1) = 1 := by
    rw [legendreSym.eq_one_iff 5 (by decide)]; decide
  rw [this]; norm_num

end LeanLab.Routes.U1451
