import LeanLab.LanguascoPintzZaccagnini2007.SPLIT_iwaniec_display16_17_1122
import LeanLab.LanguascoPintzZaccagnini2007.SPLIT_iwaniec_lemma9_numeric1122

/-!
A further split of the two HARD leaves `iwaniec_lemma9_circle16_1122` and
`iwaniec_lemma9_circle17_1122` of `SPLIT_iwaniec_display16_17_1122`, along the proof of Lemma 9
on page 102 of H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, 97 to 104,
read on the page image of `papers/Iwaniec1974.pdf`.

The printed proof is one line: from Lemma 8, page 101, for the primitive character `χ*`
inducing `χ`,
`|L(s, χ)| < η⁻¹ ∏_{p ∣ d} (1 + p^(η-1)) (d^(100η) + exp (60 l^(1/4))) < M`.
It has three steps:
* Lemma 8 for `χ*`: `η |L(s, χ*)| < d^(100η) + exp (60 l^(1/4))`, the Vinogradov input;
* the Euler factors removed from `L(s, χ*)`: `|L(s, χ)| ≤ |L(s, χ*)| ∏_{p ∣ q} (1 + p^(η-1))`
  for `Re s > 1 - η`, proved here from Mathlib's `LFunction_changeLevel`;
* the numerical inequality `η⁻¹ ∏ (1 + p^(η-1)) (d^(100η) + exp (60 l^(1/4))) ≤ M`.

Lemma 10 of page 102, the leaf `iwaniec_lemma10_1122`, is not cut: the paper proves it only by
a citation, so it stays CITED-LEFT.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- LEAF: Iwaniec 1974 page 101, Lemma 8, as page 102 uses it for Lemma 9 and page 103 in the circle before display (16).
Class: HARD.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 101, Lemma 8: for a
nonprincipal primitive `χ*` and `Re s > 1 - η`, `η |L(s, χ*)| < d^(100η) + exp (60 l^(1/4))`.
Stated for the primitive character inducing `χ`, in the circle `|s - s₀| < η`,
`s₀ = 1 + 5θ + iγ`, with `d`, `l`, `η` those of the modulus `q` at the height `γ`, as page 103
uses them; see the QUESTION in the notes. -/
theorem iwaniec_lemma8_circle16_1122 (q : ℕ) (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (γ l η θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ))))
    (s : ℂ) (hs : s ∈ Metric.ball (((1 + 5 * θ : ℝ) : ℂ) + (γ : ℂ) * Complex.I) η) :
    η * ‖Lfun481 χ.primitiveCharacter s‖ ≤
      ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ (100 * η) + Real.exp (60 * l ^ (1 / 4 : ℝ)) := by
  sorry

/-- LEAF: Iwaniec 1974 page 101, Lemma 8, as page 103 uses it in the circle before display (17).
Class: HARD.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 101, Lemma 8, for the
primitive character inducing a nonprincipal `ψ`, here `χ²`, in the circle `|s - s₁| < η/2`,
`s₁ = 1 + 5θ + 2iγ`, with `d`, `l`, `η` of the modulus `q` at the height `γ` and the factor `2`
that page 103 puts in `2M`; see the QUESTION in the notes. -/
theorem iwaniec_lemma8_circle17_1122 (q : ℕ) (hq : 3 ≤ q) (ψ : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (γ l η θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ))))
    (s : ℂ) (hs : s ∈ Metric.ball (((1 + 5 * θ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I) (η / 2)) :
    η * ‖Lfun481 ψ.primitiveCharacter s‖ ≤
      2 * (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ (100 * η) +
        Real.exp (60 * l ^ (1 / 4 : ℝ))) := by
  sorry

/-- Iwaniec 1974 page 102, the closing inequality of the proof of Lemma 9, proved from the
split in `SPLIT_iwaniec_lemma9_numeric1122`.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 102, proof of
Lemma 9: `η⁻¹ ∏_{p ∣ d} (1 + p^(η-1)) (d^(100η) + exp (60 l^(1/4))) < M` with
`M = (d^η exp l^(1/4))^100`. A floating point check over all `q < 3000`, the primorials up to
the product of the first 299 primes and powers of two, at heights up to `10^100`, gives a margin
of at least `66` in the logarithm. -/
theorem iwaniec_lemma9_numeric1122 (q : ℕ) (hq : 3 ≤ q) (γ l η M : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100) :
    η⁻¹ * (∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (η - 1))) *
      (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ (100 * η) + Real.exp (60 * l ^ (1 / 4 : ℝ))) ≤
      M := by
  have hl2 := iwaniec_l_gt_two1122 q hq γ l hl
  have hηpos : 0 < η := by
    rw [hη]
    have h1 : 0 < Real.sqrt l := Real.sqrt_pos.mpr (by linarith)
    have h2 : 0 < Real.log (2 * l) := Real.log_pos (by linarith)
    have h3 : 0 < Real.log (2 * l) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos h2 _
    positivity
  set D : ℝ := ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) with hD
  have hD1 : 1 ≤ D := by
    rw [hD]
    have : 0 < ∏ p ∈ q.primeFactors, p :=
      Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    exact_mod_cast this
  set E := Real.exp (60 * l ^ (1 / 4 : ℝ))
  set P := ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (η - 1))
  have hDp : 1 ≤ D ^ (100 * η) := Real.one_le_rpow hD1 (by positivity)
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hP0 : 0 ≤ P := Finset.prod_nonneg (fun p _ => by positivity)
  have hP : P ≤ Real.exp (5 + 2 * Real.log l) :=
    (iwaniec_lemma9_euler_exp1122 q η).trans (Real.exp_le_exp.mpr (iwaniec_lemma9_primesum1122 q hq γ l η hl hη))
  have hC := iwaniec_lemma9_final1122 q hq γ l η hl hη
  have hMeq : M = D ^ (100 * η) * Real.exp (100 * l ^ (1 / 4 : ℝ)) := by
    rw [hM, mul_pow, ← Real.rpow_mul_natCast (by linarith), ← Real.exp_nat_mul]
    norm_num [mul_comm]
  rw [hMeq]
  have hsum : D ^ (100 * η) + E ≤ D ^ (100 * η) * (1 + E) := by nlinarith
  calc η⁻¹ * P * (D ^ (100 * η) + E)
      ≤ η⁻¹ * Real.exp (5 + 2 * Real.log l) * (D ^ (100 * η) * (1 + E)) := by
        apply mul_le_mul _ hsum (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hP (by positivity)
    _ = D ^ (100 * η) * (η⁻¹ * Real.exp (5 + 2 * Real.log l) * (1 + E)) := by ring
    _ ≤ D ^ (100 * η) * Real.exp (100 * l ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hC (by linarith)

/-- Iwaniec 1974 page 102, proof of Lemma 9, the Euler factors: for `Re s > 1 - η`,
`|L(s, χ)| ≤ |L(s, χ*)| ∏_{p ∣ q} (1 + p^(η-1))`, from Mathlib's `LFunction_changeLevel`. -/
theorem iwaniec_euler_factors1122 {q : ℕ} (hq : q ≠ 0) (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (η : ℝ) (s : ℂ) (hs : 1 - η < s.re) :
    ‖Lfun481 χ s‖ ≤ ‖Lfun481 χ.primitiveCharacter s‖ *
      ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (η - 1)) := by
  haveI : NeZero q := ⟨hq⟩
  have hc : χ.conductor ≠ 0 := χ.conductor_ne_zero
  haveI : NeZero χ.conductor := ⟨hc⟩
  have hprim1 : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, h]
    exact map_one _
  have hL : Lfun481 χ s = DirichletCharacter.LFunction χ s := by
    simp only [Lfun481, dif_neg hq]
  have hL' : Lfun481 χ.primitiveCharacter s =
      DirichletCharacter.LFunction χ.primitiveCharacter s := by
    simp only [Lfun481, dif_neg hc]
  rw [hL, hL']
  conv_lhs => rw [← χ.changeLevel_primitiveCharacter]
  rw [DirichletCharacter.LFunction_changeLevel _ _ (Or.inl hprim1), norm_mul, norm_prod]
  refine mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) (fun p hp => ?_)) (norm_nonneg _)
  have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
  have hp0 : 0 < p := hp1
  calc ‖1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s)‖
      ≤ ‖(1 : ℂ)‖ + ‖χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s)‖ :=
        norm_sub_le _ _
    _ ≤ 1 + (p : ℝ) ^ (η - 1) := by
        rw [norm_one, norm_mul, Complex.norm_natCast_cpow_of_pos hp0]
        have h1 := DirichletCharacter.norm_le_one χ.primitiveCharacter (p : ZMod χ.conductor)
        have h2 : (p : ℝ) ^ (-s).re ≤ (p : ℝ) ^ (η - 1) := by
          apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp1)
          rw [Complex.neg_re]; linarith
        have h3 : 0 ≤ (p : ℝ) ^ (-s).re := Real.rpow_nonneg (by positivity) _
        nlinarith

/-- The leaf `iwaniec_lemma9_circle16_1122` of `SPLIT_iwaniec_display16_17_1122`, exact
statement, from Lemma 8 in the circle, the Euler factors and the numerical inequality. -/
theorem iwaniec_lemma9_circle16_1122_split (q : ℕ) (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (γ l η M θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ))))
    (s : ℂ) (hs : s ∈ Metric.ball (((1 + 5 * θ : ℝ) : ℂ) + (γ : ℂ) * Complex.I) η) :
    ‖Lfun481 χ s‖ ≤ M := by
  obtain ⟨hθpos, _, hηpos, _⟩ := iwaniec_params1122 q hq γ l η θ hl hη hθ
  have hq0 : q ≠ 0 := by omega
  have hre : 1 - η < s.re := by
    have h1 := Complex.re_le_norm ((((1 + 5 * θ : ℝ) : ℂ) + (γ : ℂ) * Complex.I) - s)
    have h0 : ((((1 + 5 * θ : ℝ) : ℂ) + (γ : ℂ) * Complex.I) - s).re = 1 + 5 * θ - s.re := by
      simp
    rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hs
    linarith
  have hE := iwaniec_euler_factors1122 hq0 χ hχ η s hre
  have h8 := iwaniec_lemma8_circle16_1122 q hq χ hχ γ l η θ hl hη hθ s hs
  have hN := iwaniec_lemma9_numeric1122 q hq γ l η M hl hη hM
  set P := ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (η - 1)) with hP
  set A := ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ (100 * η) + Real.exp (60 * l ^ (1 / 4 : ℝ))
  have hPnn : 0 ≤ P := Finset.prod_nonneg (fun p _ => by positivity)
  have hLs : ‖Lfun481 χ.primitiveCharacter s‖ ≤ η⁻¹ * A := by
    rw [le_inv_mul_iff₀ hηpos]; exact h8
  calc ‖Lfun481 χ s‖ ≤ ‖Lfun481 χ.primitiveCharacter s‖ * P := hE
    _ ≤ η⁻¹ * A * P := mul_le_mul_of_nonneg_right hLs hPnn
    _ = η⁻¹ * P * A := by ring
    _ ≤ M := hN

/-- The leaf `iwaniec_lemma9_circle17_1122` of `SPLIT_iwaniec_display16_17_1122`, exact
statement, from Lemma 8 in the circle, the Euler factors and the numerical inequality. -/
theorem iwaniec_lemma9_circle17_1122_split (q : ℕ) (hq : 3 ≤ q) (ψ : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (γ l η M θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ))))
    (s : ℂ) (hs : s ∈ Metric.ball (((1 + 5 * θ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I) (η / 2)) :
    ‖Lfun481 ψ s‖ ≤ 2 * M := by
  obtain ⟨hθpos, _, hηpos, _⟩ := iwaniec_params1122 q hq γ l η θ hl hη hθ
  have hq0 : q ≠ 0 := by omega
  have hre : 1 - η < s.re := by
    have h1 := Complex.re_le_norm ((((1 + 5 * θ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I) - s)
    have h0 : ((((1 + 5 * θ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I) - s).re = 1 + 5 * θ - s.re := by
      simp
    rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hs
    linarith
  have hE := iwaniec_euler_factors1122 hq0 ψ hψ η s hre
  have h8 := iwaniec_lemma8_circle17_1122 q hq ψ hψ γ l η θ hl hη hθ s hs
  have hN := iwaniec_lemma9_numeric1122 q hq γ l η M hl hη hM
  set P := ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (η - 1)) with hP
  set A := ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ (100 * η) + Real.exp (60 * l ^ (1 / 4 : ℝ))
  have hPnn : 0 ≤ P := Finset.prod_nonneg (fun p _ => by positivity)
  have hLs : ‖Lfun481 ψ.primitiveCharacter s‖ ≤ η⁻¹ * (2 * A) := by
    rw [le_inv_mul_iff₀ hηpos]; exact h8
  calc ‖Lfun481 ψ s‖ ≤ ‖Lfun481 ψ.primitiveCharacter s‖ * P := hE
    _ ≤ η⁻¹ * (2 * A) * P := mul_le_mul_of_nonneg_right hLs hPnn
    _ = 2 * (η⁻¹ * P * A) := by ring
    _ ≤ 2 * M := by linarith

end

end LeanLab.LPZ2007
