import LeanLab.LanguascoPintzZaccagnini2007.IwaniecCells1122

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

/-- LEAF: Iwaniec 1974 page 102, displays (14) and (15) of the proof of Lemma 11.
Class: MEDIUM.
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
  sorry

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
  sorry

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
