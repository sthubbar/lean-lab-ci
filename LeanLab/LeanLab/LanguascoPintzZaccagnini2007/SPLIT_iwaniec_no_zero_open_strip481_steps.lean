import LeanLab.LanguascoPintzZaccagnini2007.IwaniecCells1122
import LeanLab.PNTPort.DirichletZF.ThreeFourOne

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



private lemma iwaniecAux_log_le_harm (n : ℕ) : Real.log (n:ℝ) ≤ ∑ j ∈ Finset.range n, (1 / (j : ℝ)) := by
  have htel : (∑ j ∈ Finset.range n, (Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ)))
      = Real.log n := by
    rw [Finset.sum_range_sub (fun j : ℕ => Real.log (j:ℝ)) n]
    simp
  rw [← htel]
  refine Finset.sum_le_sum fun j hj => ?_
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · norm_num
  · have hj1 : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj0
    have hpos : 0 < ((j:ℝ)+1)/(j:ℝ) := by positivity
    have hdiv : Real.log (((j : ℝ)+1)/j) = Real.log ((j:ℝ)+1) - Real.log (j:ℝ) :=
      Real.log_div (by positivity) hj1.ne'
    have hkey : Real.log (((j:ℝ)+1)/j) ≤ ((j:ℝ)+1)/j - 1 := Real.log_le_sub_one_of_pos hpos
    have hlast : ((j:ℝ)+1)/j - 1 = 1/(j:ℝ) := by field_simp; ring
    calc Real.log ((j+1:ℕ):ℝ) - Real.log (j:ℝ) = Real.log (((j:ℝ)+1)/j) := by rw [hdiv]; push_cast; ring
      _ ≤ 1/(j:ℝ) := by rw [← hlast]; exact hkey

private lemma iwaniecAux_antitone_rpow_neg {σ : ℝ} (hσ : 0 < σ) :
    AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Ici 1) := by
  intro a ha b hb hab
  have ha1 : (1:ℝ) ≤ a := ha
  have ha0 : (0:ℝ) < a := by linarith
  have hb0 : (0:ℝ) < b := by linarith
  have hgoal : b ^ (-σ) ≤ a ^ (-σ) := by
    rw [Real.rpow_neg ha0.le, Real.rpow_neg hb0.le]
    exact inv_anti₀ (by positivity) (Real.rpow_le_rpow ha0.le hab hσ.le)
  exact hgoal

private lemma iwaniecAux_sum_Ico_rpow_le {σ : ℝ} (hσ : 1 < σ) (j N : ℕ) (hj : 1 ≤ j) :
    ∑ n ∈ Finset.Ico (j+1) N, ((n:ℝ)) ^ (-σ) ≤ (j:ℝ) ^ (1-σ) / (σ-1) := by
  have hσ0 : (0:ℝ) < σ := by linarith
  have hσ1 : (0:ℝ) < σ - 1 := by linarith
  have hjR : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  rcases le_or_gt N (j+1) with hN | hN
  · have hempty : Finset.Ico (j+1) N = ∅ := Finset.Ico_eq_empty (by omega)
    rw [hempty, Finset.sum_empty]
    have : 0 ≤ (j:ℝ) ^ (1-σ) / (σ-1) := by positivity
    linarith
  · have hjN : j ≤ N - 1 := by omega
    have hNpos : 0 < N - 1 := by omega
    have hcast : (j:ℝ) ≤ ((N-1:ℕ):ℝ) := by exact_mod_cast hjN
    have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Icc (j:ℝ) ((N-1:ℕ):ℝ)) :=
      (iwaniecAux_antitone_rpow_neg hσ0).mono (by intro x hx; exact le_trans hjR hx.1)
    have step1 : ∑ i ∈ Finset.Ico j (N-1), (((i+1:ℕ)):ℝ) ^ (-σ) ≤
        ∫ x in (j:ℝ)..((N-1:ℕ):ℝ), x ^ (-σ) :=
      AntitoneOn.sum_le_integral_Ico hjN hanti
    have hreindex : ∑ n ∈ Finset.Ico (j+1) N, ((n:ℝ)) ^ (-σ) =
        ∑ i ∈ Finset.Ico j (N-1), (((i+1:ℕ)):ℝ) ^ (-σ) := by
      rw [Finset.sum_Ico_eq_sum_range (fun n : ℕ => ((n:ℝ)) ^ (-σ)) (j+1) N,
        Finset.sum_Ico_eq_sum_range (fun i : ℕ => (((i+1:ℕ)):ℝ) ^ (-σ)) j (N-1)]
      have hlen : N - (j+1) = (N-1) - j := by omega
      rw [hlen]
      exact Finset.sum_congr rfl (fun k _ => by congr 2; omega)
    have hint : ∫ x in (j:ℝ)..((N-1:ℕ):ℝ), x ^ (-σ) =
        ((((N-1:ℕ)):ℝ) ^ (1-σ) - (j:ℝ) ^ (1-σ)) / (1-σ) := by
      have hside : (0:ℝ) ∉ Set.uIcc (j:ℝ) ((N-1:ℕ):ℝ) := by
        rw [Set.uIcc_of_le hcast]
        simp only [Set.mem_Icc, not_and, not_le]
        intro h
        linarith
      have h : ∫ x in (j:ℝ)..((N-1:ℕ):ℝ), x ^ (-σ) =
          ((((N-1:ℕ)):ℝ) ^ ((-σ)+1) - (j:ℝ) ^ ((-σ)+1)) / ((-σ)+1) :=
        integral_rpow (Or.inr ⟨by intro hc; linarith [hσ.ne'], hside⟩)
      rw [h]
      ring_nf
    have hNσ : 0 ≤ (((N-1:ℕ)):ℝ) ^ (1-σ) := by positivity
    rw [← hreindex, hint] at step1
    have heq : ((((N-1:ℕ)):ℝ) ^ (1-σ) - (j:ℝ) ^ (1-σ)) / (1-σ)
        = ((j:ℝ) ^ (1-σ) - (((N-1:ℕ)):ℝ) ^ (1-σ)) / (σ-1) := by
      rw [show (1:ℝ)-σ = -(σ-1) by ring, div_neg]
      ring
    have hval : ((j:ℝ) ^ (1-σ) - (((N-1:ℕ)):ℝ) ^ (1-σ)) / (σ-1)
        ≤ (j:ℝ) ^ (1-σ) / (σ-1) := by
      apply div_le_div_of_nonneg_right _ hσ1.le
      linarith
    rw [heq] at step1
    linarith

private lemma iwaniecAux_summable_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (n:ℝ) ^ (-σ)) := by
  have h := (Real.summable_nat_rpow_inv (p := σ)).mpr hσ
  rw [show (fun n : ℕ => (n:ℝ) ^ (-σ)) = (fun n : ℕ => ((n:ℝ) ^ σ)⁻¹) from by
    funext n; rw [Real.rpow_neg (Nat.cast_nonneg n)]]
  exact h

private lemma iwaniecAux_partial_le {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (Real.log (n:ℝ)) * (n:ℝ)^(-σ) ≤
      (∑' n : ℕ, (n:ℝ)^(-σ)) / (σ-1) := by
  have hσ1 : (0:ℝ) < σ - 1 := by linarith
  have hsumm : Summable (fun n : ℕ => (n:ℝ)^(-σ)) := iwaniecAux_summable_rpow_neg hσ
  have hstep1 : ∑ n ∈ Finset.range N, (Real.log (n:ℝ)) * (n:ℝ)^(-σ) ≤
      ∑ n ∈ Finset.range N, (∑ j ∈ Finset.range n, (1/(j:ℝ))) * (n:ℝ)^(-σ) := by
    refine Finset.sum_le_sum fun n hn => ?_
    exact mul_le_mul_of_nonneg_right (iwaniecAux_log_le_harm n) (by positivity)
  have hstep2a : ∑ n ∈ Finset.range N, (∑ j ∈ Finset.range n, (1/(j:ℝ))) * (n:ℝ)^(-σ) =
      ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range n, (1/(j:ℝ)) * (n:ℝ)^(-σ) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Finset.sum_mul]
  have hstep2 : ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range n, (1/(j:ℝ)) * (n:ℝ)^(-σ) =
      ∑ j ∈ Finset.range N, ∑ n ∈ Finset.Ico (j+1) N, (1/(j:ℝ)) * (n:ℝ)^(-σ) := by
    simp only [Finset.range_eq_Ico]
    rw [← Finset.sum_Ico_Ico_comm' (0) N (f := fun j n => (1/(j:ℝ)) * (n:ℝ)^(-σ))]
  have hstep3 : ∑ j ∈ Finset.range N, ∑ n ∈ Finset.Ico (j+1) N, (1/(j:ℝ)) * (n:ℝ)^(-σ) ≤
      ∑ j ∈ Finset.range N, ((j:ℝ)^(-σ) / (σ-1)) := by
    refine Finset.sum_le_sum fun j hj => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have h0 : (0:ℝ)^(-σ) = 0 := Real.zero_rpow (by linarith : -σ ≠ 0)
      simp [h0]
    · have hj1 : (1:ℕ) ≤ j := hj0
      have hsum : ∑ n ∈ Finset.Ico (j+1) N, (n:ℝ)^(-σ) ≤ (j:ℝ) ^ (1-σ) / (σ-1) :=
        iwaniecAux_sum_Ico_rpow_le hσ j N hj1
      have hm : ∑ n ∈ Finset.Ico (j+1) N, (1/(j:ℝ)) * (n:ℝ)^(-σ)
          = (1/(j:ℝ)) * ∑ n ∈ Finset.Ico (j+1) N, (n:ℝ)^(-σ) := by
        rw [Finset.mul_sum]
      rw [hm]
      have hjpos : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj0
      have hnonneg : 0 ≤ 1/(j:ℝ) := by positivity
      have hb := mul_le_mul_of_nonneg_left hsum hnonneg
      have heq : (1/(j:ℝ)) * ((j:ℝ) ^ (1-σ) / (σ-1)) = (j:ℝ)^(-σ) / (σ-1) := by
        have h1 : (1/(j:ℝ)) * ((j:ℝ) ^ (1-σ)) = (j:ℝ)^(-σ) := by
          rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_add hjpos]
          ring_nf
        calc (1/(j:ℝ)) * ((j:ℝ) ^ (1-σ) / (σ-1))
            = ((1/(j:ℝ)) * (j:ℝ) ^ (1-σ)) / (σ-1) := by ring
          _ = (j:ℝ)^(-σ) / (σ-1) := by rw [h1]
      rw [← heq]
      exact hb
  have hstep4 : ∑ j ∈ Finset.range N, ((j:ℝ)^(-σ) / (σ-1)) ≤
      (∑' n : ℕ, (n:ℝ)^(-σ)) / (σ-1) := by
    rw [← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ hσ1.le
    exact hsumm.sum_le_tsum (Finset.range N) (fun i _ => by positivity)
  calc ∑ n ∈ Finset.range N, (Real.log (n:ℝ)) * (n:ℝ)^(-σ)
      ≤ _ := hstep1
    _ = _ := hstep2a
    _ = _ := hstep2
    _ ≤ _ := hstep3
    _ ≤ _ := hstep4

private lemma iwaniecAux_tsum_log_bound {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, (Real.log (n:ℝ)) * (n:ℝ)^(-σ)) ≤
      (∑' n : ℕ, (n:ℝ)^(-σ)) / (σ-1) := by
  refine Real.tsum_le_of_sum_range_le (fun n => ?_) (fun N => iwaniecAux_partial_le hσ N)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : (0:ℝ) ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    positivity

private lemma iwaniecAux_term_one_eq (σ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    LSeries.term (1 : ℕ → ℂ) (σ : ℂ) n = Complex.ofReal ((n:ℝ)^(-σ)) := by
  have hmain : (((n:ℝ))^σ)⁻¹ = ((n:ℝ))^(-σ) := (Real.rpow_neg (Nat.cast_nonneg n) σ).symm
  calc LSeries.term (1 : ℕ → ℂ) (σ : ℂ) n
      = (Complex.ofReal (((n:ℝ))^σ))⁻¹ := by
        rw [LSeries.term_of_ne_zero hn]
        simp only [Pi.one_apply, one_div]
        rw [← Complex.ofReal_natCast n, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
    _ = Complex.ofReal ((((n:ℝ))^σ)⁻¹) := by rw [Complex.ofReal_inv]
    _ = Complex.ofReal (((n:ℝ))^(-σ)) := by rw [hmain]

private lemma iwaniecAux_zeta_series_re (σ : ℝ) (hσ : 1 < σ) :
    LSeries (1 : ℕ → ℂ) (σ : ℂ) = Complex.ofReal (∑' n : ℕ, (n:ℝ)^(-σ)) := by
  have hsumm : LSeriesSummable (1 : ℕ → ℂ) (σ : ℂ) := by
    rw [LSeriesSummable_one_iff]; simpa using hσ
  have hzero : ((0:ℝ))^(-σ) = 0 := Real.zero_rpow (by linarith : -σ ≠ 0)
  have hre : (LSeries (1 : ℕ → ℂ) (σ : ℂ)).re = ∑' n : ℕ, (n:ℝ)^(-σ) := by
    rw [LSeries, Complex.re_tsum hsumm]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero, hzero]
    · rw [iwaniecAux_term_one_eq σ hn]; simp
  have him : (LSeries (1 : ℕ → ℂ) (σ : ℂ)).im = 0 := by
    rw [LSeries, Complex.im_tsum hsumm]
    have h : ∀ n : ℕ, (LSeries.term (1 : ℕ → ℂ) (σ : ℂ) n).im = 0 := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [LSeries.term_zero]
      · rw [iwaniecAux_term_one_eq σ hn]; simp
    simp only [h]
    exact tsum_zero
  rw [Complex.ext_iff]
  exact ⟨hre, by simpa using him⟩

-- the logMul series
private lemma iwaniecAux_term_logMul_eq (σ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    LSeries.term (LSeries.logMul (1 : ℕ → ℂ)) (σ : ℂ) n
      = Complex.ofReal (Real.log (n:ℝ) * (n:ℝ)^(-σ)) := by
  have hmain : (((n:ℝ))^σ)⁻¹ = ((n:ℝ))^(-σ) := (Real.rpow_neg (Nat.cast_nonneg n) σ).symm
  calc LSeries.term (LSeries.logMul (1 : ℕ → ℂ)) (σ : ℂ) n
      = Complex.ofReal (Real.log (n:ℝ)) / Complex.ofReal (((n:ℝ))^σ) := by
        rw [LSeries.term_of_ne_zero hn]
        simp only [LSeries.logMul, Pi.one_apply, mul_one]
        rw [← Complex.ofReal_natCast n, ← Complex.ofReal_cpow (Nat.cast_nonneg n),
          ← Complex.ofReal_log (Nat.cast_nonneg n)]
    _ = Complex.ofReal (Real.log (n:ℝ)) * (Complex.ofReal (((n:ℝ))^σ))⁻¹ := by
        rw [div_eq_mul_inv]
    _ = Complex.ofReal (Real.log (n:ℝ) * (((n:ℝ))^σ)⁻¹) := by
        rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
    _ = Complex.ofReal (Real.log (n:ℝ) * ((n:ℝ))^(-σ)) := by rw [hmain]

private lemma iwaniecAux_logMul_series (σ : ℝ) (hσ : 1 < σ) :
    LSeries (LSeries.logMul (1 : ℕ → ℂ)) (σ : ℂ)
      = Complex.ofReal (∑' n : ℕ, Real.log (n:ℝ) * (n:ℝ)^(-σ)) := by
  have hconv : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < (σ:ℂ).re := by
    rw [LSeries.abscissaOfAbsConv_one, ← EReal.coe_one, EReal.coe_lt_coe_iff]
    simpa using hσ
  have hsumm : LSeriesSummable (LSeries.logMul (1 : ℕ → ℂ)) (σ : ℂ) :=
    LSeriesSummable_logMul_of_lt_re hconv
  have hlog0 : Real.log ((0:ℕ):ℝ) * ((0:ℕ):ℝ)^(-σ) = 0 := by
    have h0 : ((0:ℝ))^(-σ) = 0 := Real.zero_rpow (by linarith : -σ ≠ 0)
    simp [h0]
  have hre : (LSeries (LSeries.logMul (1 : ℕ → ℂ)) (σ : ℂ)).re
      = ∑' n : ℕ, Real.log (n:ℝ) * (n:ℝ)^(-σ) := by
    rw [LSeries, Complex.re_tsum hsumm]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero, hlog0]
    · rw [iwaniecAux_term_logMul_eq σ hn]; exact Complex.ofReal_re _
  have him : (LSeries (LSeries.logMul (1 : ℕ → ℂ)) (σ : ℂ)).im = 0 := by
    rw [LSeries, Complex.im_tsum hsumm]
    have h : ∀ n : ℕ, (LSeries.term (LSeries.logMul (1 : ℕ → ℂ)) (σ : ℂ) n).im = 0 := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [LSeries.term_zero]
      · rw [iwaniecAux_term_logMul_eq σ hn]; exact Complex.ofReal_im _
    simp only [h]
    exact tsum_zero
  rw [Complex.ext_iff]
  exact ⟨hre, by simpa using him⟩

private lemma iwaniecAux_zeta_logDeriv_le (σ : ℝ) (hσ : 1 < σ) :
    -(logDeriv riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + 3 := by
  have hσ1 : (0:ℝ) < σ - 1 := by linarith
  have hs : 1 < (σ:ℂ).re := by simpa using hσ
  set A : ℝ := ∑' n : ℕ, Real.log (n:ℝ) * (n:ℝ)^(-σ) with hA
  set Z : ℝ := ∑' n : ℕ, (n:ℝ)^(-σ) with hZ
  have hvm1 : LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (σ:ℂ)
      = -deriv (LSeries (1 : ℕ → ℂ)) (σ:ℂ) / LSeries (1 : ℕ → ℂ) (σ:ℂ) :=
    ArithmeticFunction.LSeries_vonMangoldt_eq hs
  have hvm2 : LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (σ:ℂ)
      = -deriv riemannZeta (σ:ℂ) / riemannZeta (σ:ℂ) :=
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have hconv : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < (σ:ℂ).re := by
    rw [LSeries.abscissaOfAbsConv_one, ← EReal.coe_one, EReal.coe_lt_coe_iff]
    simpa using hσ
  have hderiv : deriv (LSeries (1 : ℕ → ℂ)) (σ:ℂ) = -Complex.ofReal A := by
    rw [LSeries_deriv hconv, iwaniecAux_logMul_series σ hσ]
  have hval : LSeries (1 : ℕ → ℂ) (σ:ℂ) = Complex.ofReal Z := iwaniecAux_zeta_series_re σ hσ
  have hmain : -(logDeriv riemannZeta (σ:ℂ)) = Complex.ofReal (A / Z) := by
    calc -(logDeriv riemannZeta (σ:ℂ))
        = -deriv riemannZeta (σ:ℂ) / riemannZeta (σ:ℂ) := by rw [logDeriv_apply, neg_div]
      _ = LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (σ:ℂ) := hvm2.symm
      _ = -deriv (LSeries (1 : ℕ → ℂ)) (σ:ℂ) / LSeries (1 : ℕ → ℂ) (σ:ℂ) := hvm1
      _ = -(-Complex.ofReal A) / Complex.ofReal Z := by rw [hderiv, hval]
      _ = Complex.ofReal (A / Z) := by rw [neg_neg, ← Complex.ofReal_div]
  have h2 : -(logDeriv riemannZeta (σ:ℂ)).re = A / Z := by
    rw [← Complex.neg_re, hmain, Complex.ofReal_re]
  rw [h2]
  have hAZ := iwaniecAux_tsum_log_bound hσ
  have hZsumm : Summable (fun n : ℕ => (n:ℝ)^(-σ)) := iwaniecAux_summable_rpow_neg hσ
  have hZpos : 0 < Z := by
    have h1 : (1:ℝ) ≤ Z := by
      have hle := hZsumm.le_tsum 1 (fun j hj => by positivity)
      simpa [hZ] using hle
    linarith
  have hfin : A / Z ≤ 1 / (σ - 1) := by
    have h1 : A * (σ - 1) ≤ Z := by
      rw [le_div_iff₀ hσ1] at hAZ
      exact hAZ
    rw [div_le_div_iff₀ hZpos hσ1, one_mul]
    exact h1
  linarith



private lemma iwaniecAux_factor_re_nonneg {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ (logDeriv (fun t : ℂ => 1 - (p:ℂ)^(-t)) (σ:ℂ)).re := by
  have hpne : p ≠ 0 := hp.ne_zero
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0:ℝ) < p := by linarith
  -- the derivative
  have hderiv : HasDerivAt (fun t : ℂ => 1 - (p:ℂ)^(-t)) ((p:ℂ)^(-(σ:ℂ)) * Complex.log p) (σ:ℂ) := by
    have h := ((hasDerivAt_id (σ:ℂ)).neg).const_cpow (c := (p:ℂ)) (Or.inl (by exact_mod_cast hpne))
    have h2 := h.const_sub 1
    show HasDerivAt (fun t : ℂ => 1 - (p:ℂ)^(-t)) _ _
    convert h2 using 1
    · rfl
    · show _ = -((p:ℂ)^(-(σ:ℂ)) * Complex.log p * -1); ring
  rw [logDeriv_apply, hderiv.deriv]
  have hcast : (p:ℂ)^(-(σ:ℂ)) = Complex.ofReal ((p:ℝ)^(-σ)) := by
    have hexp : (-(σ:ℂ)) = ((-σ : ℝ) : ℂ) := by push_cast; ring
    have hbase : (p:ℂ) = ((p:ℝ) : ℂ) := by push_cast; ring
    rw [hbase, hexp, ← Complex.ofReal_cpow (Nat.cast_nonneg p)]
  have hlogcast : Complex.log (p:ℂ) = Complex.ofReal (Real.log p) := by
    rw [← Complex.ofReal_natCast p, Complex.ofReal_log (Nat.cast_nonneg p)]
  have hden : (1:ℂ) - Complex.ofReal ((p:ℝ)^(-σ)) = Complex.ofReal (1 - (p:ℝ)^(-σ)) := by
    rw [← Complex.ofReal_one]; push_cast; ring
  rw [hcast, hlogcast, hden, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
  have hpos : 0 < (p:ℝ)^(-σ) := Real.rpow_pos_of_pos hp0 _
  have hlt : (p:ℝ)^(-σ) < 1 := by
    have h := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith : -σ < 0)
    simpa using h
  have hl : 0 < Real.log p := Real.log_pos hp1
  positivity



private lemma iwaniecAux_cpow_ofreal_neg (p : ℕ) (σ : ℝ) :
    (p:ℂ)^(-(σ:ℂ)) = Complex.ofReal ((p:ℝ)^(-σ)) := by
  have hexp : (-(σ:ℂ)) = ((-σ : ℝ) : ℂ) := by push_cast; ring
  have hbase : (p:ℂ) = ((p:ℝ) : ℂ) := by push_cast; ring
  rw [hbase, hexp, ← Complex.ofReal_cpow (Nat.cast_nonneg p)]

private lemma iwaniecAux_principal_ge_zeta (q : ℕ) [NeZero q] (σ : ℝ) (hσ : 1 < σ) :
    (logDeriv riemannZeta (σ : ℂ)).re ≤
      (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) (σ : ℂ)).re := by
  set s : ℂ := (σ:ℂ) with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hs1 : s ≠ 1 := by
    intro h
    have h2 := congrArg Complex.re h
    simp only [hsre, Complex.one_re] at h2
    linarith
  set P : ℂ → ℂ := fun (t : ℂ) => ∏ p ∈ q.primeFactors, (1 - (p:ℂ)^(-t)) with hPdef
  -- recurrence: the LFunction of the trivial character is P * zeta near s
  have hvalall : ∀ t : ℂ, t ≠ 1 →
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) t = P t * riemannZeta t := by
    intro t ht
    rw [hPdef]
    exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta ht
  have hval : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s = P s * riemannZeta s :=
    hvalall s hs1
  have hderiv_eq : deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s
      = deriv (fun t => P t * riemannZeta t) s := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [isOpen_ne.mem_nhds hs1] with t ht
    exact hvalall t ht
  have hlogD : logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s
      = logDeriv (fun t => P t * riemannZeta t) s := by
    rw [logDeriv_apply, logDeriv_apply, hderiv_eq, hval]
  -- nonvanishing / differentiability
  have hζne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [hsre]; linarith)
  have hfacne : ∀ p ∈ q.primeFactors, (1:ℂ) - (p:ℂ)^(-s) ≠ 0 := by
    intro p hp
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1:ℝ) < p := by exact_mod_cast hp'.one_lt
    have hp0 : (0:ℝ) < p := by linarith
    intro h
    have hcast : (p:ℂ)^(-s) = Complex.ofReal ((p:ℝ)^(-σ)) := by
      rw [hsdef]; exact iwaniecAux_cpow_ofreal_neg p σ
    rw [hcast, sub_eq_zero] at h
    have hlt : (p:ℝ)^(-σ) < 1 := by
      have := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith : -σ < 0)
      simpa using this
    have h1 : Complex.ofReal ((p:ℝ)^(-σ)) = Complex.ofReal 1 := by rw [← h]; simp
    have h2 : (p:ℝ)^(-σ) = 1 := Complex.ofReal_injective h1
    linarith
  have hPne : P s ≠ 0 := by
    rw [hPdef]
    simp only
    exact Finset.prod_ne_zero_iff.mpr hfacne
  have hdiff_fac : ∀ p ∈ q.primeFactors, DifferentiableAt ℂ (fun t : ℂ => 1 - (p:ℂ)^(-t)) s := by
    intro p hp
    have hpne : p ≠ 0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
    have h := ((hasDerivAt_id s).neg).const_cpow (c := (p:ℂ)) (Or.inl (by exact_mod_cast hpne))
    exact (h.const_sub 1).differentiableAt
  have hPdiff : DifferentiableAt ℂ P s := by
    rw [hPdef]
    exact DifferentiableAt.fun_finsetProd (fun p hp => hdiff_fac p hp)
  have hmul : logDeriv (fun t => P t * riemannZeta t) s
      = logDeriv P s + logDeriv riemannZeta s :=
    logDeriv_mul s hPne hζne hPdiff (differentiableAt_riemannZeta hs1)
  have hre : 0 ≤ (logDeriv P s).re := by
    have hprod : logDeriv P s
        = logDeriv (∏ p ∈ q.primeFactors, (fun t : ℂ => 1 - (p:ℂ)^(-t))) s := by
      rw [hPdef]
      congr 1
      funext t
      rw [Finset.prod_apply]
    rw [hprod]
    rw [logDeriv_prod (fun i hi => hfacne i hi) (fun i hi => hdiff_fac i hi)]
    rw [Complex.re_sum]
    exact Finset.sum_nonneg (fun p hp => iwaniecAux_factor_re_nonneg (Nat.prime_of_mem_primeFactors hp) hσ)
  rw [hlogD, hmul, Complex.add_re]
  linarith


private lemma iwaniecAux_eq481 (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q) :
    Lfun481 ψ = DirichletCharacter.LFunction ψ := by
  funext s
  unfold Lfun481
  split_ifs with h
  · exact absurd h (NeZero.ne q)
  · rfl

private lemma iwaniecAux_341 (q : ℕ) (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (σ γ : ℝ) (hσ : 1 < σ) :
    3 * (logDeriv (Lfun481 (1 : DirichletCharacter ℂ q)) (σ : ℂ)).re +
      4 * (logDeriv (Lfun481 χ) ((σ : ℂ) + (γ : ℂ) * Complex.I)).re +
      (logDeriv (Lfun481 (χ ^ 2))
        ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re ≤ 0 := by
  haveI : NeZero q := ⟨by omega⟩
  have key := LeanLab.PNTPort.DirichletZF.three_four_one (N := q) χ hσ γ
  simp only [iwaniecAux_eq481, logDeriv_apply, neg_div, Complex.neg_re] at key ⊢
  rw [show ((2 * γ : ℝ) : ℂ) = 2 * (γ : ℂ) by push_cast; ring]
  linarith [key]

private lemma iwaniecAux_princ (q : ℕ) (hq : 3 ≤ q) (σ : ℝ) (hσ : 1 < σ) :
    (logDeriv riemannZeta (σ : ℂ)).re ≤
      (logDeriv (Lfun481 (1 : DirichletCharacter ℂ q)) (σ : ℂ)).re := by
  haveI : NeZero q := ⟨by omega⟩
  have h := iwaniecAux_principal_ge_zeta q σ hσ
  simpa only [iwaniecAux_eq481] using h

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
  haveI : NeZero q := ⟨by omega⟩
  have h341 := iwaniecAux_341 q hq χ σ γ hσ
  have hprinc := iwaniecAux_princ q hq σ hσ
  have hzeta := iwaniecAux_zeta_logDeriv_le σ hσ
  have hq9 : (9:ℝ) ≤ (q:ℝ) * (|γ| + 3) := by
    have hq' : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    nlinarith [abs_nonneg γ]
  have he2 : Real.exp 2 < 9 := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h]; nlinarith [Real.exp_pos 1, Real.exp_one_lt_d9]
  have hl2 : 2 ≤ l := by
    rw [hl, Real.le_log_iff_exp_le (by linarith)]
    linarith
  have h15 : (3/2:ℝ) ≤ Real.log (5 * l) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h : Real.exp (3/2) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  have hstep : 4 * (logDeriv (Lfun481 χ) ((σ : ℂ) + (γ : ℂ) * Complex.I)).re +
      (logDeriv (Lfun481 (χ ^ 2))
        ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re ≤
      -(3 * (logDeriv riemannZeta (σ : ℂ)).re) := by linarith
  have hstep2 : -(3 * (logDeriv riemannZeta (σ : ℂ)).re) ≤ 3 / (σ - 1) + 9 := by
    have hz := hzeta
    rw [div_eq_mul_inv] at hz ⊢
    linarith
  have hstep3 : 3 / (σ - 1) + 9 ≤ 3 / (σ - 1) + 6 * Real.log (5 * l) := by
    have h9 : (9:ℝ) ≤ 6 * Real.log (5 * l) := by linarith [h15]
    linarith
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
