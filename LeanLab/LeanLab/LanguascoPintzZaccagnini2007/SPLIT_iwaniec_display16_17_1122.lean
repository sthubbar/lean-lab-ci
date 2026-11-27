import LeanLab.LanguascoPintzZaccagnini2007.SPLIT_iwaniec_no_zero_open_strip481_steps

/-!
A further split of the two HARD leaves `iwaniec_display16_1122` and `iwaniec_display17_1122` of
`SPLIT_iwaniec_no_zero_open_strip481_steps`, along the two lines of page 103 of
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, 97 to 104, that derive
displays (16) and (17), read on the page image of `papers/Iwaniec1974.pdf`.

Each display comes from three inputs:
* Lemma 9, page 102: `|L(s, χ)| < M` in the circle about `s₀ = 1 + 5θ + iγ`, and the same for
  `χ²` about `s₁ = 1 + 5θ + 2iγ` with `2M`, as page 103 uses it;
* the lower bound at the centre, page 103: `|L(s₀, χ)|⁻¹ ≤ Σ |μ(n)| n^(-σ₀) < 1 / 5θ`;
* Lemma 10, page 102: the Landau type lower bound for `Re F'/F (s₀)`.

The assemblies below prove the exact statements of the two parent leaves from these four
leaves. The geometry, that the zero `ρ` lies in the circle of radius `η/2` about `s₀` because
`12θ < η`, that every zero of `L` has real part below one, and the algebra turning
`4 / (η/2)` into `8 / η`, is proved here.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- LEAF: Iwaniec 1974 page 102, Lemma 10.
Class: HARD.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 102, Lemma 10, a
consequence of the maximum principle: if `F` is regular in `|s - s₀| < r` and there
`|F(s)| ≤ B |F(s₀)|`, then `Re F'/F (s₀) ≥ -(4/r) log B + Σ_ρ Re 1/(s₀ - ρ)`, the sum over the
zeros in `|s - s₀| < r/2`. Stated here for any finite set `Z` of distinct zeros in that circle,
which is weaker than the printed sum since every omitted term `Re 1/(s₀ - ρ)` is nonnegative
under the hypothesis that the zeros in the circle have real part at most `re s₀`. -/
theorem iwaniec_lemma10_1122 (F : ℂ → ℂ) (s₀ : ℂ) (r B : ℝ) (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (Metric.ball s₀ r)) (hF0 : F s₀ ≠ 0)
    (hB : ∀ s ∈ Metric.ball s₀ r, ‖F s‖ ≤ B * ‖F s₀‖)
    (hzeros : ∀ z ∈ Metric.ball s₀ (r / 2), F z = 0 → z.re ≤ s₀.re)
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, ρ ∈ Metric.ball s₀ (r / 2) ∧ F ρ = 0) :
    -(4 / r) * Real.log B + ∑ ρ ∈ Z, (1 / (s₀ - ρ)).re ≤ (logDeriv F s₀).re := by
  sorry

private lemma zeta_le (σ : ℝ) (hσ : 1 < σ) :
    (∑' n : ℕ, ((n:ℝ)) ^ (-σ)) ≤ σ / (σ - 1) := by
  have hσ0 : (0:ℝ) < σ := by linarith
  have hs : Summable (fun n : ℕ => ((n:ℝ)) ^ (-σ)) := by
    have h := (Real.summable_nat_rpow_inv (p := σ)).mpr hσ
    exact h.congr (fun n => (Real.rpow_neg (Nat.cast_nonneg n) σ).symm)
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-σ)) (Set.Ici (((1:ℕ)):ℝ)) := by
    intro a ha b hb hab
    change b ^ (-σ) ≤ a ^ (-σ)
    have ha1 : (1:ℝ) ≤ a := by simpa using ha
    have ha0 : 0 < a := by linarith
    have h1 : (1:ℝ) ≤ b / a := by rw [le_div_iff₀ ha0]; linarith
    have h2 : 1 ≤ (b / a) ^ σ := Real.one_le_rpow h1 (le_of_lt hσ0)
    have h3 : (b / a) ^ (-σ) ≤ 1 := by
      rw [Real.rpow_neg (by linarith)]
      exact inv_le_one_of_one_le₀ h2
    have hbeq : b = a * (b / a) := by field_simp
    have hstep : b ^ (-σ) = (a * (b / a)) ^ (-σ) := congrArg (fun x => x ^ (-σ)) hbeq
    calc b ^ (-σ) = (a * (b / a)) ^ (-σ) := hstep
      _ = a ^ (-σ) * (b / a) ^ (-σ) := Real.mul_rpow ha0.le (by positivity)
      _ ≤ a ^ (-σ) * 1 :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg ha0.le _)
      _ = a ^ (-σ) := by ring
  have hint : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-σ)) (Set.Ioi (((1:ℕ)):ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith : -σ < -1) (by simp : (0:ℝ) < ((1:ℕ):ℝ))
  have hnn : ∀ t ∈ Set.Ioi (((1:ℕ)):ℝ), (0:ℝ) ≤ t ^ (-σ) := by
    intro t ht
    have ht' : (1:ℝ) < t := by simpa using ht
    exact Real.rpow_nonneg (le_of_lt (by linarith : (0:ℝ) < t)) _
  have key := hanti.tsum_comp_add_le_integral 1 hint hnn
  have hintval : ∫ x in Set.Ioi (((1:ℕ)):ℝ), x ^ (-σ) = 1 / (σ - 1) := by
    rw [integral_Ioi_rpow_of_lt (by linarith : -σ < -1) (c := ((1:ℕ):ℝ)) (by simp)]
    have h1 : ((1:ℕ):ℝ) ^ (-σ + 1) = 1 := by
      have : ((1:ℕ):ℝ) = 1 := by simp
      rw [this, Real.one_rpow]
    have h2 : -σ + 1 = -(σ - 1) := by ring
    rw [h1, h2, neg_div_neg_eq]
  have hs' : Summable (fun n : ℕ => ((n+1 : ℕ):ℝ) ^ (-σ)) := (summable_nat_add_iff 1).mpr hs
  have h1 := hs.tsum_eq_zero_add
  have h2 := hs'.tsum_eq_zero_add
  have hz : ((0:ℕ):ℝ) ^ (-σ) = 0 := by
    have h0 : ((0:ℕ):ℝ) = 0 := by norm_num
    rw [h0, Real.zero_rpow (by linarith : -σ ≠ 0)]
  have ho : ((1:ℕ):ℝ) ^ (-σ) = 1 := by
    have h0 : ((1:ℕ):ℝ) = 1 := by norm_num
    rw [h0, Real.one_rpow]
  rw [hintval] at key
  have hsplit : σ / (σ - 1) = 1 + 1 / (σ - 1) := by
    field_simp
    ring
  rw [h1, h2, hz, ho, hsplit]
  linarith

/-- The complex norm of the Möbius function's value is its square. -/
private lemma norm_moebius_cast (n : ℕ) :
    ‖(((ArithmeticFunction.moebius n : ℤ) : ℂ))‖ = ((ArithmeticFunction.moebius n : ℝ)) ^ 2 := by
  have hc : ((ArithmeticFunction.moebius n : ℤ) : ℂ)
      = ((ArithmeticFunction.moebius n : ℝ) : ℂ) := by push_cast; ring
  rw [hc, Complex.norm_real, Real.norm_eq_abs]
  have h1 : |((ArithmeticFunction.moebius n : ℝ))| = ((|ArithmeticFunction.moebius n| : ℤ) : ℝ) := by
    rw [Int.cast_abs]
  rw [h1, ArithmeticFunction.abs_moebius]
  have h2 : ((ArithmeticFunction.moebius n : ℝ)) ^ 2
      = (((ArithmeticFunction.moebius n) ^ 2 : ℤ) : ℝ) := by push_cast; ring
  rw [h2, ArithmeticFunction.moebius_sq]

private lemma moebius_sq_ite (n : ℕ) :
    ((ArithmeticFunction.moebius n : ℝ)) ^ 2 = (if Squarefree n then (1:ℝ) else 0) := by
  have h : ((ArithmeticFunction.moebius n : ℝ)) ^ 2
      = (((ArithmeticFunction.moebius n) ^ 2 : ℤ) : ℝ) := by push_cast; ring
  rw [h, ArithmeticFunction.moebius_sq]
  split_ifs <;> norm_num

private lemma moebius_sq_le_one_sub (n : ℕ) :
    ((ArithmeticFunction.moebius n : ℝ)) ^ 2 ≤ 1 - (if 4 ∣ n then (1:ℝ) else 0) := by
  rw [moebius_sq_ite]
  by_cases h4 : 4 ∣ n
  · have hnsq : ¬ Squarefree n := by
      intro hs
      have hu : IsUnit (2:ℕ) := hs 2 (by rw [show 2 * 2 = 4 by norm_num]; exact h4)
      rw [Nat.isUnit_iff] at hu
      omega
    rw [if_neg hnsq, if_pos h4]
    norm_num
  · rw [if_neg h4]
    split_ifs <;> norm_num

/-- The Möbius-squared sum is at most `1/(σ-1)` on `1 < σ ≤ 6/5`. -/
private lemma mu_sq_le (σ : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 6 / 5) :
    (∑' n : ℕ, ((ArithmeticFunction.moebius n : ℝ)) ^ 2 * ((n:ℝ)) ^ (-σ)) ≤ 1 / (σ - 1) := by
  have hσ0 : (0:ℝ) < σ := by linarith
  have hσ1 : 0 < σ - 1 := by linarith
  have hsZ : Summable (fun n : ℕ => ((n:ℝ)) ^ (-σ)) := by
    have h := (Real.summable_nat_rpow_inv (p := σ)).mpr hσ
    exact h.congr (fun n => (Real.rpow_neg (Nat.cast_nonneg n) σ).symm)
  have hZ := zeta_le σ hσ
  have hZpos : (0:ℝ) ≤ ∑' n : ℕ, ((n:ℝ)) ^ (-σ) :=
    tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hA : Summable (fun n : ℕ => (if 4 ∣ n then (1:ℝ) else 0) * ((n:ℝ)) ^ (-σ)) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsZ
    · have hnn : (0:ℝ) ≤ ((n:ℝ)) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      split_ifs <;> nlinarith
    · have hnn : (0:ℝ) ≤ ((n:ℝ)) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      split_ifs <;> nlinarith
  have hfix : Summable (fun n : ℕ => (1 - (if 4 ∣ n then (1:ℝ) else 0)) * ((n:ℝ)) ^ (-σ)) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsZ
    · have hnn : (0:ℝ) ≤ ((n:ℝ)) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      split_ifs <;> nlinarith
    · have hnn : (0:ℝ) ≤ ((n:ℝ)) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      split_ifs <;> nlinarith
  have hterm : ∀ n : ℕ, ((ArithmeticFunction.moebius n : ℝ)) ^ 2 * ((n:ℝ)) ^ (-σ)
      ≤ (1 - (if 4 ∣ n then (1:ℝ) else 0)) * ((n:ℝ)) ^ (-σ) := by
    intro n
    have hnn : (0:ℝ) ≤ ((n:ℝ)) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hc := moebius_sq_le_one_sub n
    nlinarith [hc, hnn]
  have hSsum : Summable
      (fun n : ℕ => ((ArithmeticFunction.moebius n : ℝ)) ^ 2 * ((n:ℝ)) ^ (-σ)) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) hterm hfix
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hS := Summable.tsum_le_tsum hterm hSsum hfix
  have hsplit : (∑' n : ℕ, (1 - (if 4 ∣ n then (1:ℝ) else 0)) * ((n:ℝ)) ^ (-σ))
      = (∑' n : ℕ, ((n:ℝ)) ^ (-σ))
        - ∑' n : ℕ, (if 4 ∣ n then (1:ℝ) else 0) * ((n:ℝ)) ^ (-σ) := by
    rw [← Summable.tsum_sub hsZ hA]
    apply tsum_congr
    intro n
    ring
  have hfour : (4:ℝ) ^ (-σ) * (∑' n : ℕ, ((n:ℝ)) ^ (-σ))
      ≤ ∑' n : ℕ, (if 4 ∣ n then (1:ℝ) else 0) * ((n:ℝ)) ^ (-σ) := by
    have hinj : Function.Injective (fun m : ℕ => 4 * m) := by
      intro a b h
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
    have hmul : ∀ m : ℕ, (((4 * m : ℕ)):ℝ) ^ (-σ) = (4:ℝ) ^ (-σ) * ((m:ℝ)) ^ (-σ) := by
      intro m
      push_cast
      rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg m)]
    have hf : Summable (fun m : ℕ => (((4 * m : ℕ)):ℝ) ^ (-σ)) := by
      have h := hsZ.mul_left ((4:ℝ) ^ (-σ))
      exact h.congr (fun m => (hmul m).symm)
    have hkey := Summable.tsum_le_tsum_of_inj
      (f := fun m : ℕ => (((4 * m : ℕ)):ℝ) ^ (-σ))
      (g := fun n : ℕ => (if 4 ∣ n then (1:ℝ) else 0) * ((n:ℝ)) ^ (-σ))
      (fun m => 4 * m) hinj
      (by
        intro c hc
        have hnn : (0:ℝ) ≤ ((c:ℝ)) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg c) _
        split_ifs <;> nlinarith)
      (by
        intro m
        have hd : 4 ∣ 4 * m := ⟨m, by ring⟩
        rw [if_pos hd]
        simp)
      hf hA
    have hconv : (∑' m : ℕ, (((4 * m : ℕ)):ℝ) ^ (-σ))
        = (4:ℝ) ^ (-σ) * (∑' n : ℕ, ((n:ℝ)) ^ (-σ)) := by
      rw [← tsum_mul_left (a := (4:ℝ) ^ (-σ))]
      exact tsum_congr (fun m => hmul m)
    rw [hconv] at hkey
    exact hkey
  have h45 : (1:ℝ) / 5.3 ≤ (4:ℝ) ^ (-σ) := by
    have h4pos : (0:ℝ) < (4:ℝ) ^ σ := Real.rpow_pos_of_pos (by norm_num) σ
    have hle : (4:ℝ) ^ σ ≤ 5.3 := by
      have h1 : (4:ℝ) ^ σ ≤ (4:ℝ) ^ (6 / 5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ'
      have h2 : (4:ℝ) ^ (6 / 5 : ℝ) ≤ 5.3 := by
        have hp : ((4:ℝ) ^ (6 / 5 : ℝ)) ^ 5 = (4:ℝ) ^ 6 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          norm_num
        have h5 : ((4:ℝ) ^ (6 / 5 : ℝ)) ^ 5 ≤ (5.3:ℝ) ^ 5 := by
          rw [hp]
          norm_num
        exact le_of_pow_le_pow_left₀ (by norm_num : (5:ℕ) ≠ 0) (by norm_num) h5
      linarith
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4), one_div]
    exact (inv_le_inv₀ (by norm_num : (0:ℝ) < 5.3) h4pos).mpr hle
  calc (∑' n : ℕ, ((ArithmeticFunction.moebius n : ℝ)) ^ 2 * ((n:ℝ)) ^ (-σ))
      ≤ (∑' n : ℕ, ((n:ℝ)) ^ (-σ))
        - ∑' n : ℕ, (if 4 ∣ n then (1:ℝ) else 0) * ((n:ℝ)) ^ (-σ) := by
        rw [← hsplit]
        exact hS
    _ ≤ (∑' n : ℕ, ((n:ℝ)) ^ (-σ)) - (4:ℝ) ^ (-σ) * (∑' n : ℕ, ((n:ℝ)) ^ (-σ)) := by
        linarith [hfour]
    _ = (1 - (4:ℝ) ^ (-σ)) * (∑' n : ℕ, ((n:ℝ)) ^ (-σ)) := by ring
    _ ≤ (1 - (1:ℝ) / 5.3) * (∑' n : ℕ, ((n:ℝ)) ^ (-σ)) := by
        exact mul_le_mul_of_nonneg_right (by linarith) hZpos
    _ ≤ (1 - (1:ℝ) / 5.3) * (σ / (σ - 1)) :=
        mul_le_mul_of_nonneg_left hZ (by norm_num)
    _ ≤ 1 / (σ - 1) := by
        have hc : (1 - (1:ℝ) / 5.3) = 43 / 53 := by norm_num
        rw [hc, mul_div_assoc', div_le_div_iff₀ hσ1 hσ1]
        nlinarith

/-- LEAF: Iwaniec 1974 page 103, the bound at the centre used for displays (16) and (17).
Class: MEDIUM.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 103, the line before
display (16): `|L(s₀, χ)|⁻¹ ≤ Σ |μ(n)| n^(-σ₀) < 1 / (σ₀ - 1)`, from the Euler product, with
`σ₀ = 1 + 5θ`. Stated for every character and `1 < σ ≤ 6/5`; on that range
`ζ(σ) / ζ(2σ) ≤ 1 / (σ - 1)`. -/
theorem iwaniec_centre_lower1122 (q : ℕ) (hq : 1 ≤ q) (ψ : DirichletCharacter ℂ q)
    (σ t : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 6 / 5) :
    σ - 1 ≤ ‖Lfun481 ψ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  haveI : NeZero q := ⟨by omega⟩
  set s : ℂ := (σ:ℂ) + (t:ℂ) * Complex.I with hsdef
  have hre : s.re = σ := by simp [hsdef]
  have hs : 1 < s.re := by rw [hre]; exact hσ
  set Gf : ℕ → ℂ := fun n => ψ n with hGf
  set Mf : ℕ → ℂ := fun n => ((ArithmeticFunction.moebius n : ℂ)) with hMf
  have hLfun : Lfun481 ψ s = LSeries Gf s := by
    have h := DirichletCharacter.LFunction_eq_LSeries ψ hs
    simp only [Lfun481, dif_neg (by omega : q ≠ 0)]
    simpa [hGf] using h
  have hprod : LSeries Gf s * LSeries (Gf * Mf) s = 1 := by
    have h := DirichletCharacter.LSeries.mul_mu_eq_one ψ hs
    simpa [hGf, hMf] using h
  have hsumm2 : LSeriesSummable (Gf * Mf) s := by
    have h := DirichletCharacter.LSeriesSummable_mul ψ
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
    simpa [hGf, hMf] using h
  have hsZ : Summable (fun n : ℕ => ((n:ℝ)) ^ (-σ)) := by
    have h := (Real.summable_nat_rpow_inv (p := σ)).mpr hσ
    exact h.congr (fun n => (Real.rpow_neg (Nat.cast_nonneg n) σ).symm)
  have hSsum : Summable (fun n : ℕ => ((ArithmeticFunction.moebius n : ℝ)) ^ 2 * ((n:ℝ)) ^ (-σ)) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsZ
    · exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    · have h1 : ((ArithmeticFunction.moebius n : ℝ)) ^ 2 ≤ 1 := by
        rw [moebius_sq_ite]
        split_ifs <;> norm_num
      have h2 : (0:ℝ) ≤ ((n:ℝ)) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      nlinarith [h1, h2]
  have hpt : ∀ n : ℕ, ‖LSeries.term (Gf * Mf) s n‖
      ≤ ((ArithmeticFunction.moebius n : ℝ)) ^ 2 * ((n:ℝ)) ^ (-σ) := by
    intro n
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [if_neg hn, hre]
    have hpsi : ‖ψ n‖ ≤ 1 := DirichletCharacter.norm_le_one ψ n
    have hmu : ‖(((ArithmeticFunction.moebius n : ℤ) : ℂ))‖
        = ((ArithmeticFunction.moebius n : ℝ)) ^ 2 := norm_moebius_cast n
    have hval : (Gf * Mf) n = ψ n * ((ArithmeticFunction.moebius n : ℤ) : ℂ) := by
      simp only [Pi.mul_apply, hGf, hMf]
    have hnum : ‖(Gf * Mf) n‖ ≤ ((ArithmeticFunction.moebius n : ℝ)) ^ 2 := by
      rw [hval, norm_mul, hmu]
      have hnn : (0:ℝ) ≤ ((ArithmeticFunction.moebius n : ℝ)) ^ 2 := by positivity
      nlinarith [hpsi, hnn]
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hden : (0:ℝ) < (n:ℝ) ^ σ := Real.rpow_pos_of_pos hnpos σ
    rw [Real.rpow_neg (Nat.cast_nonneg n), div_le_iff₀ hden]
    have hc : ((ArithmeticFunction.moebius n : ℝ)) ^ 2 * ((n:ℝ) ^ σ)⁻¹ * (n:ℝ) ^ σ
        = ((ArithmeticFunction.moebius n : ℝ)) ^ 2 := by
      rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hden), mul_one]
    rw [hc]
    exact hnum
  have hnorm : ‖LSeries (Gf * Mf) s‖
      ≤ ∑' n : ℕ, ((ArithmeticFunction.moebius n : ℝ)) ^ 2 * ((n:ℝ)) ^ (-σ) := by
    have h1 := norm_tsum_le_tsum_norm hsumm2.norm
    exact le_trans h1 (Summable.tsum_le_tsum hpt hsumm2.norm hSsum)
  have hprod' : ‖LSeries Gf s‖ * ‖LSeries (Gf * Mf) s‖ = 1 := by
    rw [← norm_mul, hprod, norm_one]
  have hS := mu_sq_le σ hσ hσ'
  have hle : (1:ℝ) ≤ ‖LSeries Gf s‖ * (1 / (σ - 1)) :=
    calc (1:ℝ) = ‖LSeries Gf s‖ * ‖LSeries (Gf * Mf) s‖ := hprod'.symm
      _ ≤ ‖LSeries Gf s‖ * (1 / (σ - 1)) :=
          mul_le_mul_of_nonneg_left (le_trans hnorm hS) (norm_nonneg _)
  rw [mul_one_div, le_div_iff₀ (by linarith : (0:ℝ) < σ - 1)] at hle
  rw [hLfun]
  linarith

/-- LEAF: Iwaniec 1974 page 102, Lemma 9, as page 103 applies it before display (16).
Class: HARD.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 102, Lemma 9, from
Theorem 1 of page 97: for a nonprincipal `χ` modulo `q ≥ 3`, `|L(s, χ)| < M` where
`Re s > 1 - η`. Page 103 uses it in the circle `|s - s₀| < η`, `s₀ = 1 + 5θ + iγ`, with `l`, `η`,
`M` taken at the height `γ`; see the QUESTION in the notes on this choice of height. -/
theorem iwaniec_lemma9_circle16_1122 (q : ℕ) (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (γ l η M θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ))))
    (s : ℂ) (hs : s ∈ Metric.ball (((1 + 5 * θ : ℝ) : ℂ) + (γ : ℂ) * Complex.I) η) :
    ‖Lfun481 χ s‖ ≤ M := by
  sorry

/-- LEAF: Iwaniec 1974 page 103, Lemma 9 as applied before display (17).
Class: HARD.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 103, the sentence
before display (17): for a nonprincipal `ψ`, here `χ²`, `L(s, ψ)` satisfies
`|L(s, ψ)| ≤ 2M` in the circle `|s - s₁| < η/2`, `s₁ = 1 + 5θ + 2iγ`, with `l`, `η`, `M` taken at
the height `γ`. From Lemma 9 of page 102; see the QUESTION in the notes on the factor `2`. -/
theorem iwaniec_lemma9_circle17_1122 (q : ℕ) (hq : 3 ≤ q) (ψ : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (γ l η M θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ))))
    (s : ℂ) (hs : s ∈ Metric.ball (((1 + 5 * θ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I) (η / 2)) :
    ‖Lfun481 ψ s‖ ≤ 2 * M := by
  sorry

/-- The size facts of page 102 for the parameters: `0 < θ ≤ 1/25`, `0 < η` and `12 θ < η`,
the last because `θ = η / (400 log M)` and `log M ≥ 100`. -/
theorem iwaniec_params1122 (q : ℕ) (hq : 3 ≤ q) (γ l η θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ)))) :
    0 < θ ∧ θ ≤ 1 / 25 ∧ 0 < η ∧ 12 * θ < η := by
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
  have hL1 : 1 ≤ Real.log (2 * l) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith
  set L := Real.log (2 * l) with hL
  have hd : (1 : ℝ) ≤ ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
    have : 0 < ∏ p ∈ q.primeFactors, p :=
      Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    exact_mod_cast this
  have hlogd : 0 ≤ Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := Real.log_nonneg hd
  set D := Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) with hD
  have hl0 : (0 : ℝ) ≤ l := by linarith
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hsplit : (l * L) ^ (3 / 4 : ℝ) = l ^ (3 / 4 : ℝ) * L ^ (3 / 4 : ℝ) :=
    Real.mul_rpow hl0 hL0
  have hlpow : l ^ (1 / 2 : ℝ) ≤ l ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hsqrt : Real.sqrt l = l ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow l
  have hLpow : 1 ≤ L ^ (3 / 4 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hlhalf : 1 ≤ l ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hl34 : 1 ≤ l ^ (3 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hP : 1 ≤ (l * L) ^ (3 / 4 : ℝ) := by
    rw [hsplit]; exact one_le_mul_of_one_le_of_one_le hl34 hLpow
  have hden : 1 ≤ D + (l * L) ^ (3 / 4 : ℝ) := by linarith
  have hθpos : 0 < θ := by rw [hθ]; positivity
  have hθle : θ ≤ 1 / 25 := by
    rw [hθ, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set E := l ^ (1 / 2 : ℝ) * L ^ (3 / 4 : ℝ) with hE
  have hEpos : 1 ≤ E := by rw [hE]; exact one_le_mul_of_one_le_of_one_le hlhalf hLpow
  have hηE : η = 1 / E := by rw [hη, hsqrt, hE]; exact (one_div _).symm
  have hηpos : 0 < η := by rw [hηE]; positivity
  have hEle : E ≤ (l * L) ^ (3 / 4 : ℝ) := by
    rw [hsplit, hE]
    exact mul_le_mul_of_nonneg_right hlpow (by linarith)
  refine ⟨hθpos, hθle, hηpos, ?_⟩
  rw [hθ, hηE, mul_one_div, div_lt_div_iff₀ (by positivity) (by linarith)]
  linarith

/-- `Lfun481` agrees with Mathlib's `LFunction` for a positive modulus. -/
theorem iwaniec_Lfun_eq1122 {q : ℕ} (hq : q ≠ 0) (ψ : DirichletCharacter ℂ q) :
    Lfun481 ψ = (haveI : NeZero q := ⟨hq⟩; DirichletCharacter.LFunction ψ) := by
  funext s
  simp only [Lfun481, dif_neg hq]

/-- For a nonprincipal character the zeros of `Lfun481` have real part below one, and the
function is differentiable everywhere. -/
theorem iwaniec_Lfun_facts1122 {q : ℕ} (hq : q ≠ 0) (ψ : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) :
    Differentiable ℂ (Lfun481 ψ) ∧ ∀ z : ℂ, Lfun481 ψ z = 0 → z.re < 1 := by
  haveI : NeZero q := ⟨hq⟩
  rw [iwaniec_Lfun_eq1122 hq ψ]
  refine ⟨DirichletCharacter.differentiable_LFunction hψ, ?_⟩
  intro z hz
  by_contra h
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) (not_lt.mp h) hz

/-- A character with a nonreal value is nonprincipal. -/
theorem iwaniec_ne_one_of_nonreal1122 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hnonreal : ∃ a, (χ a).im ≠ 0) : χ ≠ 1 := by
  rintro rfl
  obtain ⟨a, ha⟩ := hnonreal
  apply ha
  by_cases hu : IsUnit a
  · simp [MulChar.one_apply hu]
  · simp [MulChar.map_nonunit _ hu]

/-- Display (16) of page 103, the exact statement of `iwaniec_display16_1122`, from Lemma 9 in
the circle about `s₀`, the bound at the centre, and Lemma 10 with the zero `ρ = s`. -/
theorem iwaniec_display16_1122_split (q : ℕ) (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (hnonreal : ∃ a, (χ a).im ≠ 0) (s : ℂ) (l η M θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|s.im| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ))))
    (hzero : Lfun481 χ s = 0) (hreg : 1 - θ < s.re) (hlt : s.re < 1) :
    -(4 / η) * Real.log (M / (5 * θ)) + 1 / (1 + 5 * θ - s.re) ≤
      (logDeriv (Lfun481 χ) (((1 + 5 * θ : ℝ) : ℂ) + (s.im : ℂ) * Complex.I)).re := by
  obtain ⟨hθpos, hθle, hηpos, h12⟩ := iwaniec_params1122 q hq s.im l η θ hl hη hθ
  have hq0 : q ≠ 0 := by omega
  have hχ := iwaniec_ne_one_of_nonreal1122 χ hnonreal
  obtain ⟨hdiff, hre⟩ := iwaniec_Lfun_facts1122 hq0 χ hχ
  set s₀ : ℂ := ((1 + 5 * θ : ℝ) : ℂ) + (s.im : ℂ) * Complex.I with hs₀
  have hc := iwaniec_centre_lower1122 q (by omega) χ (1 + 5 * θ) s.im (by linarith)
    (by linarith)
  have hc' : 5 * θ ≤ ‖Lfun481 χ s₀‖ := by
    have : (1 + 5 * θ) - 1 = 5 * θ := by ring
    rw [this] at hc; exact hc
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  have hF0 : Lfun481 χ s₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hc'; linarith
  have hB : ∀ z ∈ Metric.ball s₀ η, ‖Lfun481 χ z‖ ≤ M / (5 * θ) * ‖Lfun481 χ s₀‖ := by
    intro z hz
    have h1 := iwaniec_lemma9_circle16_1122 q hq χ hχ s.im l η M θ hl hη hM hθ z hz
    have h2 : M ≤ M / (5 * θ) * ‖Lfun481 χ s₀‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left hc' hMnn
    linarith
  have hdiffS : s₀ - s = (((1 + 5 * θ - s.re : ℝ)) : ℂ) := by
    apply Complex.ext <;> simp [hs₀]
  have hsball : s ∈ Metric.ball s₀ (η / 2) := by
    rw [Metric.mem_ball, dist_comm, dist_eq_norm, hdiffS, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hzeros : ∀ z ∈ Metric.ball s₀ (η / 2), Lfun481 χ z = 0 → z.re ≤ s₀.re := by
    intro z _ hz
    have := hre z hz
    have : s₀.re = 1 + 5 * θ := by simp [hs₀]
    linarith
  have key := iwaniec_lemma10_1122 (Lfun481 χ) s₀ η (M / (5 * θ)) hηpos
    hdiff.differentiableOn hF0 hB hzeros {s} (by
      intro ρ hρ
      rw [Finset.mem_singleton] at hρ
      subst hρ
      exact ⟨hsball, hzero⟩)
  rw [Finset.sum_singleton, hdiffS] at key
  have hre1 : (1 / (((1 + 5 * θ - s.re : ℝ)) : ℂ)).re = 1 / (1 + 5 * θ - s.re) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hre1] at key
  exact key

/-- Display (17) of page 103, the exact statement of `iwaniec_display17_1122`, from Lemma 9 in
the circle about `s₁` for `χ²`, the bound at the centre, and Lemma 10 with no zero. -/
theorem iwaniec_display17_1122_split (q : ℕ) (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (hnonreal : ∃ a, (χ a).im ≠ 0) (γ l η M θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ)))) :
    -(8 / η) * Real.log (2 * M / (5 * θ)) ≤
      (logDeriv (Lfun481 (χ ^ 2)) (((1 + 5 * θ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re := by
  obtain ⟨hθpos, hθle, hηpos, _⟩ := iwaniec_params1122 q hq γ l η θ hl hη hθ
  have hq0 : q ≠ 0 := by omega
  have hψ := iwaniec_sq_ne_one_of_nonreal1122 χ hnonreal
  obtain ⟨hdiff, hre⟩ := iwaniec_Lfun_facts1122 hq0 (χ ^ 2) hψ
  set s₁ : ℂ := ((1 + 5 * θ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I with hs₁
  have hc := iwaniec_centre_lower1122 q (by omega) (χ ^ 2) (1 + 5 * θ) (2 * γ) (by linarith)
    (by linarith)
  have hc' : 5 * θ ≤ ‖Lfun481 (χ ^ 2) s₁‖ := by
    have : (1 + 5 * θ) - 1 = 5 * θ := by ring
    rw [this] at hc; exact hc
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  have hF0 : Lfun481 (χ ^ 2) s₁ ≠ 0 := by
    intro h; rw [h, norm_zero] at hc'; linarith
  have hB : ∀ z ∈ Metric.ball s₁ (η / 2),
      ‖Lfun481 (χ ^ 2) z‖ ≤ 2 * M / (5 * θ) * ‖Lfun481 (χ ^ 2) s₁‖ := by
    intro z hz
    have h1 := iwaniec_lemma9_circle17_1122 q hq (χ ^ 2) hψ γ l η M θ hl hη hM hθ z hz
    have h2 : 2 * M ≤ 2 * M / (5 * θ) * ‖Lfun481 (χ ^ 2) s₁‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left hc' (by linarith)
    linarith
  have hzeros : ∀ z ∈ Metric.ball s₁ (η / 2 / 2), Lfun481 (χ ^ 2) z = 0 → z.re ≤ s₁.re := by
    intro z _ hz
    have := hre z hz
    have : s₁.re = 1 + 5 * θ := by simp [hs₁]
    linarith
  have key := iwaniec_lemma10_1122 (Lfun481 (χ ^ 2)) s₁ (η / 2) (2 * M / (5 * θ))
    (by linarith) hdiff.differentiableOn hF0 hB hzeros ∅ (by simp)
  rw [Finset.sum_empty, add_zero] at key
  have h48 : 4 / (η / 2) = 8 / η := by field_simp; ring
  rw [h48] at key
  exact key

end

end LeanLab.LPZ2007
