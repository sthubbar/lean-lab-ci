import LeanLab.LanguascoPintzZaccagnini2007.SPLIT_iwaniec_display14_15_1122

/-!
A split of the open strip step `iwaniec_no_zero_open_strip481` of
`SPLIT_iwaniec_zero_free481`, and with it of the four parameter cells of
`SPLIT_iwaniec_no_zero_open_strip481`, along the PROOF of Iwaniec 1974, Lemma 11, step (i),
pages 102 and 103 of papers/Iwaniec1974.pdf, read on the page images. The cells cut the
parameter range; this file cuts the argument instead.

Source: H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, 97 to 104.
Page 97: `q ≥ 3`, `d = ∏_{p ∣ q} p`, `l = log q (|t| + 3)`, `η⁻¹ = √l (log 2l) ^ (3/4)`.
Page 102, Lemma 9: `M = (d ^ η exp l ^ (1/4)) ^ 100`. Lemma 11: `θ = η / (400 log M)`, which
equals the printed `1 / (4·10⁴ (log d + (l log 2l) ^ (3/4)))` of page 97, proved as
`iwaniec_theta_identity1122`; the leaves below use the printed page 97 form of `θ`.

Step (i) of Lemma 11 for a character with `χ² ≠ χ₀`, which every character with a nonreal
value has, `iwaniec_sq_ne_one_of_nonreal1122`. A zero `ρ = β + iγ` with `β > 1 - θ`, the
points `σ₀ = 1 + 5θ`, `s₀ = σ₀ + iγ`, `s₁ = σ₀ + 2iγ`:
* display (16), page 103, from Lemma 9 and Lemma 10 for `L(s, χ)` around `s₀`;
* display (17), page 103, from Lemma 9 and Lemma 10 for `L(s, χ²)` around `s₁`;
* displays (14) and (15), page 102, the 3-4-1 inequality with the principal character term
  bounded below;
* the closing numerical inequality of page 103, `... ≤ 1 / (15 θ)`.
The assembly `iwaniec_printed_nonreal_split1122` combines the four by real algebra alone:
`4 / (σ₀ - β) ≤ 3 / (5θ) + 1 / (15θ)`, so `σ₀ - β ≥ 6θ` and `β ≤ 1 - θ`. Points with real part
at least one are handled by Mathlib's `LFunction_ne_zero_of_one_le_re`. The lab statement then
follows from `iwaniecStatement481_of_printed1122`, and the open strip step and each of the four
cells follow from it.

Lemma 9 itself, which holds the Vinogradov input Lemmas 4 and 5, sits inside the leaves for
displays (16) and (17).

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- LEAF: Iwaniec 1974 page 103, Lemma 11 step (i), display (16).
Class: HARD.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 103, display (16),
from Lemma 9 page 102 and Lemma 10 page 102. For `χ ≠ χ₀` modulo `q ≥ 3`, a zero `ρ = s` of
`L(s, χ)` with `β > 1 - θ`, `σ₀ = 1 + 5θ`, `s₀ = σ₀ + iγ`:
`Re L'/L (s₀, χ) ≥ -(4/η) log (M / 5θ) + 1 / (σ₀ - β)`. -/
theorem iwaniec_display16_1122 (q : ℕ) (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (hnonreal : ∃ a, (χ a).im ≠ 0) (s : ℂ) (l η M θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|s.im| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ))))
    (hzero : Lfun481 χ s = 0) (hreg : 1 - θ < s.re) (hlt : s.re < 1) :
    -(4 / η) * Real.log (M / (5 * θ)) + 1 / (1 + 5 * θ - s.re) ≤
      (logDeriv (Lfun481 χ) (((1 + 5 * θ : ℝ) : ℂ) + (s.im : ℂ) * Complex.I)).re := by
  sorry

/-- LEAF: Iwaniec 1974 page 103, Lemma 11 step (i), display (17).
Class: HARD.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 103, display (17),
from Lemma 9 page 102 applied to `χ²`, nonprincipal since `χ` has a nonreal value, and
Lemma 10 page 102. With `σ₀ = 1 + 5θ`, `s₁ = σ₀ + 2iγ`:
`Re L'/L (s₁, χ²) ≥ -(8/η) log (2M / 5θ)`. The paper uses `M` at the height `γ` of the zero
also around `s₁`; see the QUESTION in the notes. -/
theorem iwaniec_display17_1122 (q : ℕ) (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (hnonreal : ∃ a, (χ a).im ≠ 0) (γ l η M θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ)))) :
    -(8 / η) * Real.log (2 * M / (5 * θ)) ≤
      (logDeriv (Lfun481 (χ ^ 2)) (((1 + 5 * θ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re := by
  sorry

/-- Iwaniec 1974 page 102, displays (14) and (15) of the proof of Lemma 11, formerly a MEDIUM
leaf, now proved from the leaves `iwaniec_display14_1122` and `iwaniec_display15_1122` of
`SPLIT_iwaniec_display14_15_1122`.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 102: display (14),
`3 Re L'/L (σ, χ₀) + 4 Re L'/L (σ + it, χ) + Re L'/L (σ + 2it, χ²) ≤ 0` for `σ > 1`, and
display (15) at the real point `σ`, `Re L'/L (σ, χ₀) ≥ -1/(σ - 1) - 2 log 5l`, from
`|ζ'/ζ (σ) + 1/(σ - 1)| < 3` and `|L'/L (σ, χ₀) - ζ'/ζ (σ)| < 2 log log 3d`. Here `l` is taken at
any height `γ`, since `log 3d ≤ l` for every `γ`. -/
theorem iwaniec_display14_15_1122 (q : ℕ) (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (γ l σ : ℝ) (hl : l = Real.log ((q : ℝ) * (|γ| + 3))) (hσ : 1 < σ) :
    4 * (logDeriv (Lfun481 χ) ((σ : ℂ) + (γ : ℂ) * Complex.I)).re +
      (logDeriv (Lfun481 (χ ^ 2)) ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re ≤
      3 / (σ - 1) + 6 * Real.log (5 * l) := by
  have h14 := iwaniec_display14_1122 q hq χ γ σ hσ
  have h15 := iwaniec_display15_1122 q hq γ l σ hl hσ
  have h3 : 3 * (1 / (σ - 1)) = 3 / (σ - 1) := by ring
  linarith

/-- LEAF: Iwaniec 1974 page 103, the closing numerical step of Lemma 11 step (i).
Class: MEDIUM.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 103, the line after
display (17): `6 log 5l + (16/η) log (M / 5θ) + (8/η) log (2M / 5θ) ≤ 1 / (15 θ)`, with
`θ = η / (400 log M)` of page 102 in its printed page 97 form, `iwaniec_theta_identity1122`.
A floating point check over `log d` up to `10⁵` and `l` from `log 9` to `10⁸` gives a ratio of
left to right side at most about `0.96`. -/
theorem iwaniec_closing_numeric1122 (q : ℕ) (hq : 3 ≤ q) (γ l η M θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ)))) :
    6 * Real.log (5 * l) + (16 / η) * Real.log (M / (5 * θ)) +
      (8 / η) * Real.log (2 * M / (5 * θ)) ≤ 1 / (15 * θ) := by
  have hq' : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have ht : 0 ≤ |γ| := abs_nonneg _
  have hbase : (9 : ℝ) ≤ (q : ℝ) * (|γ| + 3) := by nlinarith
  have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he2 : Real.exp 2 < 9 := by
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith [Real.exp_pos 1]
  have hl2 : 2 ≤ l := by
    rw [hl, Real.le_log_iff_exp_le (by linarith)]
    linarith
  have hl0 : 0 < l := by linarith
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (2 * l) := ⟨_, rfl⟩
  rw [← hL] at hη hθ
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by linarith)]
    linarith
  obtain ⟨D, hD⟩ : ∃ D, D = Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hD] at hθ
  have hd : (1 : ℝ) ≤ ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
    have : 0 < ∏ p ∈ q.primeFactors, p :=
      Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    exact_mod_cast this
  have hD0 : 0 ≤ D := by rw [hD]; exact Real.log_nonneg hd
  obtain ⟨u, hu⟩ : ∃ u, u = l ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  have hu1 : 1 ≤ u := by rw [hu]; exact Real.one_le_rpow (by linarith) (by norm_num)
  obtain ⟨E, hE⟩ : ∃ E, E = Real.sqrt l * L ^ (3 / 4 : ℝ) := ⟨_, rfl⟩
  rw [← hE] at hη
  have hsqrt1 : 1 ≤ Real.sqrt l := by
    rw [Real.le_sqrt (by norm_num) hl0.le]; linarith
  have hLp : 1 ≤ L ^ (3 / 4 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hE1 : 1 ≤ E := by rw [hE]; exact one_le_mul_of_one_le_of_one_le hsqrt1 hLp
  have hE0 : 0 < E := by linarith
  have hηE : η * E = 1 := by rw [hη]; field_simp
  -- P = E u
  have hP : (l * L) ^ (3 / 4 : ℝ) = E * u := by
    rw [Real.mul_rpow hl0.le (by linarith), hE, hu, Real.sqrt_eq_rpow]
    have : l ^ (3 / 4 : ℝ) = l ^ (1 / 2 : ℝ) * l ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hl0]; norm_num
    rw [this]; ring
  rw [hP] at hθ
  obtain ⟨X, hX⟩ : ∃ X, X = D + E * u := ⟨_, rfl⟩
  rw [← hX] at hθ
  have hEu : 1 ≤ E * u := one_le_mul_of_one_le_of_one_le hE1 hu1
  have hX1 : 1 ≤ X := by rw [hX]; linarith
  have hX0 : 0 < X := by linarith
  have hθpos : 0 < θ := by rw [hθ]; positivity
  -- log M
  have hdpos : (0 : ℝ) < ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by linarith
  have hMpos : 0 < M := by rw [hM]; positivity
  have hlogM : Real.log M = 100 * (η * D + u) := by
    rw [hM, Real.log_pow, Real.log_mul (Real.rpow_pos_of_pos hdpos _).ne' (Real.exp_pos _).ne',
      Real.log_rpow hdpos, Real.log_exp, ← hD, ← hu]
    push_cast; ring
  have h5θ : 5 * θ = 1 / (8000 * X) := by rw [hθ]; field_simp; ring
  have hlog5θ : Real.log (5 * θ) = -Real.log (8000 * X) := by
    rw [h5θ, one_div, Real.log_inv]
  have hA : Real.log (M / (5 * θ)) = Real.log M + Real.log (8000 * X) := by
    rw [Real.log_div hMpos.ne' (by positivity), hlog5θ]; ring
  have hB : Real.log (2 * M / (5 * θ)) = Real.log 2 + Real.log M + Real.log (8000 * X) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) hMpos.ne',
      hlog5θ]; ring
  have h16 : 16 / η = 16 * E := by rw [hη]; field_simp
  have h8 : 8 / η = 8 * E := by rw [hη]; field_simp
  have hR : 1 / (15 * θ) = 40000 * X / 15 := by rw [hθ]; field_simp; ring
  have hEM : E * Real.log M = 100 * X := by
    rw [hlogM, hX]
    have : E * (100 * (η * D + u)) = 100 * ((η * E) * D + E * u) := by ring
    rw [this, hηE]; ring
  -- scalar bounds
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog5 : Real.log 5 ≤ 3 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hlog8000 : Real.log 8000 ≤ 13 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hlu : Real.log u = (1 / 4) * Real.log l := by rw [hu, Real.log_rpow hl0]
  have hlu' : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hll : Real.log l ≤ 4 * (u - 1) := by linarith
  have hLL : Real.log L ≤ L - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hLeq : L = Real.log 2 + Real.log l := by rw [hL, Real.log_mul (by norm_num) hl0.ne']
  have h5l : Real.log (5 * l) = Real.log 5 + Real.log l := Real.log_mul (by norm_num) hl0.ne'
  have h5l0 : 0 ≤ Real.log (5 * l) := Real.log_nonneg (by linarith)
  have hlogP : Real.log (E * u) = (3 / 4) * (Real.log l + Real.log L) := by
    rw [← hP, Real.log_rpow (by positivity), Real.log_mul hl0.ne' (by positivity)]
  have hS : 6 * Real.log (5 * l) + 24 * (Real.log 8000 + Real.log (E * u)) + 8 * Real.log 2 ≤
      (800 / 3) * u := by
    rw [h5l, hlogP]; linarith
  have hlam : Real.log (8000 * X) = Real.log 8000 + Real.log X :=
    Real.log_mul (by norm_num) hX0.ne'
  have hXP : Real.log X - Real.log (E * u) ≤ X / (E * u) - 1 := by
    rw [← Real.log_div hX0.ne' (by positivity)]
    exact Real.log_le_sub_one_of_pos (by positivity)
  have hEX : E * (X / (E * u) - 1) ≤ D := by
    have : E * (X / (E * u) - 1) = D / u := by
      rw [hX]; field_simp; ring
    rw [this]; exact div_le_self hD0 hu1
  have hK : 6 * Real.log (5 * l) + 24 * E * Real.log (8000 * X) + 8 * E * Real.log 2 ≤
      (800 / 3) * X := by
    have h1 := mul_le_mul_of_nonneg_left hS hE0.le
    have h2 : E * (Real.log X - Real.log (E * u)) ≤ E * (X / (E * u) - 1) :=
      mul_le_mul_of_nonneg_left hXP hE0.le
    have h3 : 6 * Real.log (5 * l) ≤ E * (6 * Real.log (5 * l)) := by
      have := mul_le_mul_of_nonneg_right hE1 (by linarith : (0:ℝ) ≤ 6 * Real.log (5 * l))
      linarith
    rw [hlam]
    linarith [h1, h2, hEX, h3, hX]
  rw [hA, hB, h16, h8, hR]
  have : 6 * Real.log (5 * l) + 16 * E * (Real.log M + Real.log (8000 * X)) +
      8 * E * (Real.log 2 + Real.log M + Real.log (8000 * X)) =
      6 * Real.log (5 * l) + 24 * E * Real.log (8000 * X) + 8 * E * Real.log 2 +
        24 * (E * Real.log M) := by ring
  rw [this, hEM]
  linarith

/-- The printed denominator of page 97 is positive for `q ≥ 3`. -/
theorem iwaniec_printed_theta_pos1122 (q : ℕ) (hq : 3 ≤ q) (γ : ℝ) :
    0 < 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (Real.log ((q : ℝ) * (|γ| + 3)) *
        Real.log (2 * Real.log ((q : ℝ) * (|γ| + 3)))) ^ (3 / 4 : ℝ))) := by
  have hq' : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have ht : 0 ≤ |γ| := abs_nonneg _
  have hbase : (3 : ℝ) ≤ (q : ℝ) * (|γ| + 3) := by nlinarith
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hl1 : 1 < Real.log ((q : ℝ) * (|γ| + 3)) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    linarith
  have hl2 : 0 < Real.log (2 * Real.log ((q : ℝ) * (|γ| + 3))) :=
    Real.log_pos (by linarith)
  have hpow : 0 < (Real.log ((q : ℝ) * (|γ| + 3)) *
      Real.log (2 * Real.log ((q : ℝ) * (|γ| + 3)))) ^ (3 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (mul_pos (by linarith) hl2) _
  have hd : (1 : ℝ) ≤ ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
    have : 0 < ∏ p ∈ q.primeFactors, p :=
      Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    exact_mod_cast this
  have hlogd : 0 ≤ Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := Real.log_nonneg hd
  have : 0 < Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (Real.log ((q : ℝ) * (|γ| + 3)) *
        Real.log (2 * Real.log ((q : ℝ) * (|γ| + 3)))) ^ (3 / 4 : ℝ) := by linarith
  positivity

/-- The printed Theorem 2 of page 97 for characters with a nonreal value, assembled from the
four steps of Lemma 11 step (i): displays (16), (17), (14) with (15), and the closing
numerical inequality. -/
theorem iwaniec_printed_nonreal_split1122 (r : ℕ) (hr : 3 ≤ r) (χ : DirichletCharacter ℂ r)
    (hnonreal : ∃ a, (χ a).im ≠ 0) (s : ℂ)
    (hs : 1 - 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ r.primeFactors, p : ℕ) : ℝ) +
        (Real.log ((r : ℝ) * (|s.im| + 3)) *
          Real.log (2 * Real.log ((r : ℝ) * (|s.im| + 3)))) ^ (3 / 4 : ℝ))) < s.re) :
    Lfun481 χ s ≠ 0 := by
  have hr0 : r ≠ 0 := by omega
  rcases le_or_gt 1 s.re with hge | hlt
  · haveI : NeZero r := ⟨hr0⟩
    have hne : χ ≠ 1 := by
      rintro rfl
      obtain ⟨a, ha⟩ := hnonreal
      apply ha
      by_cases hu : IsUnit a
      · simp [MulChar.one_apply hu]
      · simp [MulChar.map_nonunit _ hu]
    have hL : Lfun481 χ s = DirichletCharacter.LFunction χ s := by
      simp only [Lfun481, dif_neg hr0]
    rw [hL]
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) hge
  · intro hzero
    have hθpos := iwaniec_printed_theta_pos1122 r hr s.im
    obtain ⟨l, hl⟩ : ∃ l, l = Real.log ((r : ℝ) * (|s.im| + 3)) := ⟨_, rfl⟩
    obtain ⟨η, hη⟩ : ∃ η, η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹ := ⟨_, rfl⟩
    obtain ⟨M, hM⟩ : ∃ M, M = (((∏ p ∈ r.primeFactors, p : ℕ) : ℝ) ^ η *
        Real.exp (l ^ (1 / 4 : ℝ))) ^ 100 := ⟨_, rfl⟩
    obtain ⟨θ, hθ⟩ : ∃ θ, θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ r.primeFactors, p : ℕ) : ℝ) +
        (l * Real.log (2 * l)) ^ (3 / 4 : ℝ))) := ⟨_, rfl⟩
    have hθ' : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ r.primeFactors, p : ℕ) : ℝ) +
        (Real.log ((r : ℝ) * (|s.im| + 3)) *
          Real.log (2 * Real.log ((r : ℝ) * (|s.im| + 3)))) ^ (3 / 4 : ℝ))) := by
      rw [hθ, hl]
    rw [← hθ'] at hs hθpos
    have hA := iwaniec_display16_1122 r hr χ hnonreal s l η M θ hl hη hM hθ hzero hs hlt
    have hB := iwaniec_display17_1122 r hr χ hnonreal s.im l η M θ hl hη hM hθ
    have hC := iwaniec_display14_15_1122 r hr χ s.im l (1 + 5 * θ) hl (by linarith)
    have hD := iwaniec_closing_numeric1122 r hr s.im l η M θ hl hη hM hθ
    have hC' : 4 * (logDeriv (Lfun481 χ) (((1 + 5 * θ : ℝ) : ℂ) + (s.im : ℂ) * Complex.I)).re +
        (logDeriv (Lfun481 (χ ^ 2))
          (((1 + 5 * θ : ℝ) : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I)).re ≤
        3 / (5 * θ) + 6 * Real.log (5 * l) := by
      have h5 : (1 + 5 * θ) - 1 = 5 * θ := by ring
      rw [h5] at hC
      exact hC
    set x := 1 + 5 * θ - s.re with hx
    have hxpos : 0 < x := by rw [hx]; linarith
    have hkey : 4 / x ≤ 3 / (5 * θ) + 1 / (15 * θ) := by
      have h4 : 4 * (1 / x) = 4 / x := by ring
      have hm : 4 * ((4 / η) * Real.log (M / (5 * θ))) =
          (16 / η) * Real.log (M / (5 * θ)) := by ring
      linarith [hA, hB, hC', hD, hm, h4]
    have hsum : 3 / (5 * θ) + 1 / (15 * θ) = 2 / (3 * θ) := by
      field_simp
      ring
    rw [hsum, div_le_div_iff₀ hxpos (by positivity)] at hkey
    have : 6 * θ ≤ x := by linarith
    rw [hx] at this
    linarith

/-- The lab statement `IwaniecStatement481` from the four steps of Lemma 11 step (i). -/
theorem iwaniecStatement481_steps1122 : IwaniecStatement481 :=
  iwaniecStatement481_of_printed1122 (fun r hr χ hnonreal s hs =>
    iwaniec_printed_nonreal_split1122 r hr χ hnonreal s hs)

/-- The exact statement of `iwaniec_no_zero_open_strip481` of `SPLIT_iwaniec_zero_free481`,
assembled from the four steps. -/
theorem iwaniec_no_zero_open_strip481_steps (r : ℕ) (hr : 1 ≤ r)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive) (hnonreal : ∃ a, (χ a).im ≠ 0)
    {s : ℂ} (hlt : s.re < 1) (hpos : 0 < s.re)
    (hreg : 1 - 1 / iwaniecDenom481 r s.im < s.re) : Lfun481 χ s ≠ 0 :=
  iwaniecStatement481_steps1122 r hr χ hprim hnonreal s hreg

/-- The exact statement of the cell `iwaniec_no_zero_strip_small_modulus_bounded_height481`
of `SPLIT_iwaniec_no_zero_open_strip481`, from the four steps. -/
theorem iwaniec_no_zero_strip_small_modulus_bounded_height481_steps
    (r : ℕ) (hr : 1 ≤ r) (hmod : r ≤ 10 ^ 4)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive)
    (hnonreal : ∃ a, (χ a).im ≠ 0) {s : ℂ}
    (hlt : s.re < 1) (hpos : 0 < s.re)
    (hreg : 1 - 1 / iwaniecDenom481 r s.im < s.re)
    (hheight : |s.im| ≤ 2) : Lfun481 χ s ≠ 0 :=
  iwaniecStatement481_steps1122 r hr χ hprim hnonreal s hreg

/-- The exact statement of the cell `iwaniec_no_zero_strip_large_modulus_bounded_height481`
of `SPLIT_iwaniec_no_zero_open_strip481`, from the four steps. -/
theorem iwaniec_no_zero_strip_large_modulus_bounded_height481_steps
    (r : ℕ) (hr : 1 ≤ r) (hmod : 10 ^ 4 ≤ r)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive)
    (hnonreal : ∃ a, (χ a).im ≠ 0) {s : ℂ}
    (hlt : s.re < 1) (hpos : 0 < s.re)
    (hreg : 1 - 1 / iwaniecDenom481 r s.im < s.re)
    (hheight : |s.im| ≤ 2) : Lfun481 χ s ≠ 0 :=
  iwaniecStatement481_steps1122 r hr χ hprim hnonreal s hreg

/-- The exact statement of the cell `iwaniec_no_zero_strip_small_modulus_large_height481`
of `SPLIT_iwaniec_no_zero_open_strip481`, from the four steps. -/
theorem iwaniec_no_zero_strip_small_modulus_large_height481_steps
    (r : ℕ) (hr : 1 ≤ r) (hmod : r ≤ 10 ^ 4)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive)
    (hnonreal : ∃ a, (χ a).im ≠ 0) {s : ℂ}
    (hlt : s.re < 1) (hpos : 0 < s.re)
    (hreg : 1 - 1 / iwaniecDenom481 r s.im < s.re)
    (hheight : 2 ≤ |s.im|) : Lfun481 χ s ≠ 0 :=
  iwaniecStatement481_steps1122 r hr χ hprim hnonreal s hreg

/-- The exact statement of the cell `iwaniec_no_zero_strip_large_modulus_large_height481`
of `SPLIT_iwaniec_no_zero_open_strip481`, from the four steps. -/
theorem iwaniec_no_zero_strip_large_modulus_large_height481_steps
    (r : ℕ) (hr : 1 ≤ r) (hmod : 10 ^ 4 ≤ r)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive)
    (hnonreal : ∃ a, (χ a).im ≠ 0) {s : ℂ}
    (hlt : s.re < 1) (hpos : 0 < s.re)
    (hreg : 1 - 1 / iwaniecDenom481 r s.im < s.re)
    (hheight : 2 ≤ |s.im|) : Lfun481 χ s ≠ 0 :=
  iwaniecStatement481_steps1122 r hr χ hprim hnonreal s hreg

end

end LeanLab.LPZ2007
