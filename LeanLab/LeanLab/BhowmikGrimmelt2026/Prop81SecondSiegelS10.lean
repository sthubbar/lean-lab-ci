/-
S10-07, ROUTE BURST burst-20261124. `leaf_count_second` of `SPLIT_prop81.lean` forces the
absence of Landau-Siegel zeros.

The leaf `leaf_count_second` asks that the single character term
`𝔖(χ,χ,N) B(1-δ,1-δ) N^(2(1-δ)-1)` exceed half of the Prop 8.1 threshold on at most
`C_ε X^(3/5+ε)` even `N` of the window `[X/2, X]`. P0029 page 30 display 8.1, second formula,
gives `𝔖(χ,χ,N) = χ(-1) 𝔖(N)` whenever the conductor `r` divides `N`; this is `facts81_diag`
of `SPLIT_facts81.lean`, proved with no open leaf. Page 32 uses that `B(β,β) N^(-2δ)` is close to
`1`. So on every even multiple of `r` in the window the character term has size about
`𝔖(N) N`, above the threshold once `δ log X` is tiny, `r / φ(r)²` is at most `1/8` and `X` is
large. With `ϑ = 2/5`, `ε = 1/30` and `X = 4 r³` there are more than `r²` such `N`, while
`C_ε X^(19/30)` is of order `r^(19/10)`.

The theorem `leaf_count_second_forces_no_siegel_S10` below proves, with no open leaf: the
statement of `leaf_count_second` implies that there are `c > 0` and `r₀` such that no
primitive real character of conductor `r ≥ r₀` with `φ(r)² ≥ 8 r` has a real zero `1 - δ`
with `0 < δ < c / log r`. The constant is `c = 16^(-10)/4`. The side condition
`φ(r)² ≥ 8 r` holds for every prime `r ≥ 11`, see `prime_totient_sq_S10`, and for all large
`r`; the absence of such zeros even for prime conductors is the Landau-Siegel problem, which is
OPEN. So `leaf_count_second` is not provable without settling an open problem, and the split
`prop81_split` is not a faithful split of Prop 8.1: the paper keeps `r₂(N) - 𝔖(N) N - T(N)`
together, display 8.3, and the two leaves bound the two pieces apart.

The file is not a refutation: no Landau-Siegel zero is known, so `leaf_count_second` is not
shown false. The file imports `Decomp150a` only for the public `singular_ge_one461`, and
`SPLIT_prop81` only for a final type check that the hypothesis is the leaf's statement.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.BhowmikGrimmelt2026.Statements
import LeanLab.BhowmikGrimmelt2026.SPLIT_facts81
import LeanLab.BhowmikGrimmelt2026.Decomp150a
import LeanLab.BhowmikGrimmelt2026.SPLIT_prop81

namespace LeanLab.BhowmikGrimmelt2026

open Real

/-- `Γ(β) ≥ 1` for `0 < β ≤ 1`, from the convexity of `Γ` on `(0, ∞)` and `Γ(1) = Γ(2) = 1`:
`1` is the convex combination of `β` and `2` with weights `1/(2-β)` and `(1-β)/(2-β)`. -/
theorem one_le_Gamma_S10 {β : ℝ} (h0 : 0 < β) (h1 : β ≤ 1) : 1 ≤ Real.Gamma β := by
  have hd : 0 < 2 - β := by linarith
  have ha : 0 ≤ 1 / (2 - β) := by positivity
  have hb : 0 ≤ (1 - β) / (2 - β) := div_nonneg (by linarith) hd.le
  have hab : 1 / (2 - β) + (1 - β) / (2 - β) = 1 := by
    field_simp
    ring
  have hconv := Real.convexOn_Gamma.2 (show β ∈ Set.Ioi (0:ℝ) from h0)
    (show (2:ℝ) ∈ Set.Ioi (0:ℝ) by norm_num) ha hb hab
  have hpt : (1 / (2 - β)) • β + ((1 - β) / (2 - β)) • (2:ℝ) = 1 := by
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [hpt, Real.Gamma_one, Real.Gamma_two] at hconv
  simp only [smul_eq_mul, mul_one] at hconv
  have hm : (2 - β) * 1 ≤ (2 - β) * (1 / (2 - β) * Real.Gamma β + (1 - β) / (2 - β)) :=
    mul_le_mul_of_nonneg_left hconv hd.le
  have e : (2 - β) * (1 / (2 - β) * Real.Gamma β + (1 - β) / (2 - β)) =
      Real.Gamma β + (1 - β) := by
    field_simp
  linarith

/-- `Γ(s) ≤ 1` for `1 ≤ s ≤ 2`, from the convexity of `Γ` and `Γ(1) = Γ(2) = 1`. -/
theorem Gamma_le_one_S10 {s : ℝ} (h1 : 1 ≤ s) (h2 : s ≤ 2) : Real.Gamma s ≤ 1 := by
  have hconv := Real.convexOn_Gamma.2 (show (1:ℝ) ∈ Set.Ioi (0:ℝ) by norm_num)
    (show (2:ℝ) ∈ Set.Ioi (0:ℝ) by norm_num) (show (0:ℝ) ≤ 2 - s by linarith)
    (show (0:ℝ) ≤ s - 1 by linarith) (by ring)
  have hpt : (2 - s) • (1:ℝ) + (s - 1) • (2:ℝ) = s := by
    simp only [smul_eq_mul]
    ring
  rw [hpt, Real.Gamma_one, Real.Gamma_two] at hconv
  simp only [smul_eq_mul] at hconv
  linarith

/-- The Beta factor of page 32: `|B(β,β)| = Γ(β)²/Γ(2β) ≥ 1` for `1/2 ≤ β ≤ 1`, with `betaC`
as in `Statements.lean`. P0029 page 32 uses `B(β,β) = 1 + O(c)`; the one-sided bound is all the
count needs. -/
theorem one_le_norm_betaC_S10 {β : ℝ} (h0 : 1 / 2 ≤ β) (h1 : β ≤ 1) :
    1 ≤ ‖betaC ((β : ℝ) : ℂ) ((β : ℝ) : ℂ)‖ := by
  have hG := one_le_Gamma_S10 (by linarith : 0 < β) h1
  have hG2 := Gamma_le_one_S10 (s := 2 * β) (by linarith) (by linarith)
  have hpos : 0 < Real.Gamma (2 * β) := Real.Gamma_pos_of_pos (by linarith)
  have hval : betaC ((β : ℝ) : ℂ) ((β : ℝ) : ℂ) =
      ((Real.Gamma β * Real.Gamma β / Real.Gamma (2 * β) : ℝ) : ℂ) := by
    unfold betaC
    rw [show ((β : ℝ) : ℂ) + ((β : ℝ) : ℂ) = ((2 * β : ℝ) : ℂ) by push_cast; ring,
      Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.ofReal_div, Complex.ofReal_mul]
  have hq : 1 ≤ Real.Gamma β * Real.Gamma β / Real.Gamma (2 * β) := by
    rw [le_div_iff₀ hpos]
    nlinarith
  rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  exact hq

/-- Display 8.1, second formula, page 30, in norm: for a primitive real `χ` of conductor `r`
dividing the even `N ≥ 2`, `|𝔖(χ,χ,N)| = 𝔖(N)`. From `facts81_diag` and `facts81_base`. -/
theorem norm_genSing_diag_S10 (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r)
    (hprim : χ.IsPrimitive) (hreal : IsRealChar χ) (N : ℕ) (hEven : Even N) (hN2 : 2 ≤ N)
    (hdvd : r ∣ N) : ‖genSing χ χ N‖ = singular N := by
  rw [facts81_diag r χ hprim hreal N hEven hN2 hdvd, facts81_base N hEven hN2, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (facts81_pos N hEven hN2)]
  have h : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul, neg_mul_neg, one_mul, map_one]
  have hn : ‖χ (-1)‖ * ‖χ (-1)‖ = 1 := by rw [← norm_mul, h, norm_one]
  have h1 : ‖χ (-1)‖ = 1 :=
    (mul_self_eq_one_iff.mp hn).resolve_right (fun h' => by linarith [norm_nonneg (χ (-1))])
  rw [h1, one_mul]

/-- The pointwise lower bound, the page 32 computation run with the leaf's threshold: on an
even multiple `N` of the conductor in `[X/2, X]`, with `X > 2^40`, `δ log X ≤ 16^(-10)` and
`φ(r)² ≥ 8 r`, the character term `𝔖(χ,χ,N) B(1-δ,1-δ) N^(1-2δ)` is larger than half of the
Prop 8.1 threshold with the constants `h = 1/2`, `c' = ε₀ = 1/10`, `C = 4` of `SPLIT_prop81`. -/
theorem char_term_large_S10 (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r)
    (hprim : χ.IsPrimitive) (hreal : IsRealChar χ)
    (htot : 8 * (r : ℝ) ≤ (Nat.totient r : ℝ) ^ 2)
    (X δ : ℝ) (hX : (2 : ℝ) ^ 40 < X) (hδ : 0 < δ)
    (hη : δ * Real.log X ≤ (1 / 16) ^ 10)
    (N : ℕ) (hEven : Even N) (hdvd : r ∣ N) (hNlo : X / 2 ≤ N) (hNhi : (N : ℝ) ≤ X) :
    ¬ ‖genSing χ χ N * betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ) *
                (N : ℂ) ^ (2 * ((1 - δ : ℝ) : ℂ) - 1)‖ ≤
            (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
                singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
                  X ^ (1 - (1 : ℝ) / 10)) / 2 := by
  have h240 : (0 : ℝ) < 2 ^ 40 := by positivity
  have hXpos : 0 < X := by linarith
  have hNpos' : (0 : ℝ) < N := by linarith
  have hNpos : 0 < N := by exact_mod_cast hNpos'
  have hN2 : 2 ≤ N := by
    have h4 : (4 : ℝ) ≤ 2 ^ 40 := by norm_num
    have : (2 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hS1 : (1 : ℝ) ≤ singular N := singular_ge_one461 N hEven hNpos
  have hS0 : (0 : ℝ) ≤ singular N := by linarith
  -- `log X ≥ 1`
  have hlog1 : 1 ≤ Real.log X := by
    have h1 : Real.log ((2 : ℝ) ^ 40) ≤ Real.log X := Real.log_le_log h240 hX.le
    rw [Real.log_pow] at h1
    have h2 := Real.log_two_gt_d9
    push_cast at h1
    linarith
  have hlogX0 : 0 < Real.log X := by linarith
  have hδsmall : δ ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_left hlog1 hδ.le
    have h3 : ((1 : ℝ) / 16) ^ 10 ≤ 1 / 4 := by norm_num
    linarith
  -- the Beta factor
  have hB : 1 ≤ ‖betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ)‖ :=
    one_le_norm_betaC_S10 (by linarith) (by linarith)
  -- the power
  have hre : (2 * ((1 - δ : ℝ) : ℂ) - 1).re = 1 - 2 * δ := by
    simp <;> ring
  have hpow : ‖(N : ℂ) ^ (2 * ((1 - δ : ℝ) : ℂ) - 1)‖ = (N : ℝ) ^ (1 - 2 * δ) := by
    rw [Complex.norm_natCast_cpow_of_pos hNpos, hre]
  have hpowlow : (3 / 4) * (N : ℝ) ≤ (N : ℝ) ^ (1 - 2 * δ) := by
    have hsplit : (N : ℝ) ^ (1 - 2 * δ) = (N : ℝ) * (N : ℝ) ^ (-(2 * δ)) := by
      rw [show (1 : ℝ) - 2 * δ = 1 + (-(2 * δ)) by ring, Real.rpow_add hNpos', Real.rpow_one]
    have hexp : (N : ℝ) ^ (-(2 * δ)) = Real.exp (Real.log N * (-(2 * δ))) :=
      Real.rpow_def_of_pos hNpos' _
    have hlogN : Real.log N ≤ Real.log X := Real.log_le_log hNpos' hNhi
    have hge : 3 / 4 ≤ (N : ℝ) ^ (-(2 * δ)) := by
      rw [hexp]
      have h1 := Real.add_one_le_exp (Real.log N * (-(2 * δ)))
      have h2 : δ * Real.log N ≤ δ * Real.log X := mul_le_mul_of_nonneg_left hlogN hδ.le
      have h3 : ((1 : ℝ) / 16) ^ 10 ≤ 1 / 8 := by norm_num
      nlinarith
    rw [hsplit]
    nlinarith
  -- the norm of the character term
  have hT : (3 / 4) * (singular N * N) ≤
      ‖genSing χ χ N * betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ) *
                (N : ℂ) ^ (2 * ((1 - δ : ℝ) : ℂ) - 1)‖ := by
    rw [norm_mul, norm_mul, norm_genSing_diag_S10 r χ hprim hreal N hEven hN2 hdvd, hpow]
    have hP0 : 0 ≤ (N : ℝ) ^ (1 - 2 * δ) := Real.rpow_nonneg hNpos'.le _
    have e1 : singular N * 1 ≤ singular N * ‖betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hB hS0
    have e2 : singular N * ((3 / 4) * (N : ℝ)) ≤ singular N * (N : ℝ) ^ (1 - 2 * δ) :=
      mul_le_mul_of_nonneg_left hpowlow hS0
    have e3 : singular N * (N : ℝ) ^ (1 - 2 * δ) ≤
        singular N * ‖betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ)‖ * (N : ℝ) ^ (1 - 2 * δ) := by
      have := mul_le_mul_of_nonneg_right e1 hP0
      linarith
    linarith
  -- the first threshold term
  have hη0 : 0 ≤ δ * Real.log X := mul_nonneg hδ.le hlogX0.le
  have hroot : (δ * Real.log X) ^ ((1 : ℝ) / 10) ≤ 1 / 16 := by
    have h1 := Real.rpow_le_rpow hη0 hη (by norm_num : (0 : ℝ) ≤ 1 / 10)
    have h2 : (((1 : ℝ) / 16) ^ (10 : ℕ)) ^ (((10 : ℕ) : ℝ)⁻¹) = 1 / 16 :=
      Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
    rw [show ((1 : ℝ) / 10) = ((10 : ℕ) : ℝ)⁻¹ by norm_num, h2] at h1
    rw [show ((1 : ℝ) / 10) = ((10 : ℕ) : ℝ)⁻¹ by norm_num]
    exact h1
  have hSX0 : 0 ≤ singular N * X := mul_nonneg hS0 hXpos.le
  have t1 : singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) ≤ singular N * X * (1 / 16) :=
    mul_le_mul_of_nonneg_left hroot hSX0
  -- the conductor term
  have hr0 : (0 : ℝ) < r := by exact_mod_cast NeZero.pos r
  have hφ : (0 : ℝ) < (Nat.totient r : ℝ) ^ 2 := by linarith
  have hSN0 : 0 ≤ singular N * N := mul_nonneg hS0 hNpos'.le
  have t2 : singular N * N * r / (Nat.totient r : ℝ) ^ 2 ≤ singular N * N / 8 := by
    rw [div_le_iff₀ hφ]
    have := mul_le_mul_of_nonneg_left htot hSN0
    nlinarith
  -- the power term
  have hX10 : 16 < X ^ ((1 : ℝ) / 10) := by
    have h1 := Real.rpow_lt_rpow h240.le hX (by norm_num : (0 : ℝ) < 1 / 10)
    have h2 : ((16 : ℝ) ^ (10 : ℕ)) ^ (((10 : ℕ) : ℝ)⁻¹) = 16 :=
      Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
    rw [show ((2 : ℝ) ^ 40) = (16 : ℝ) ^ (10 : ℕ) by norm_num,
      show ((1 : ℝ) / 10) = ((10 : ℕ) : ℝ)⁻¹ by norm_num, h2] at h1
    rw [show ((1 : ℝ) / 10) = ((10 : ℕ) : ℝ)⁻¹ by norm_num]
    exact h1
  have hXsplit : X ^ (1 - (1 : ℝ) / 10) * X ^ ((1 : ℝ) / 10) = X := by
    rw [← Real.rpow_add hXpos]
    norm_num
  have hP9 : 0 < X ^ (1 - (1 : ℝ) / 10) := Real.rpow_pos_of_pos hXpos _
  have t3 : 16 * X ^ (1 - (1 : ℝ) / 10) < X := by
    have := mul_lt_mul_of_pos_left hX10 hP9
    linarith
  -- comparison
  have hX2N : X ≤ 2 * N := by linarith
  have c1 : singular N * X ≤ singular N * (2 * N) := mul_le_mul_of_nonneg_left hX2N hS0
  have c2 : (N : ℝ) ≤ singular N * N := by nlinarith
  intro hle
  nlinarith

/-- `φ(p)² ≥ 8 p` for a prime `p ≥ 11`, so the side condition of the main theorem holds on all
large prime conductors. -/
theorem prime_totient_sq_S10 (p : ℕ) (hp : p.Prime) (h11 : 11 ≤ p) :
    8 * (p : ℝ) ≤ (Nat.totient p : ℝ) ^ 2 := by
  rw [Nat.totient_prime hp]
  have h1 : 1 ≤ p := by omega
  have h11' : (11 : ℝ) ≤ p := by exact_mod_cast h11
  push_cast [h1]
  nlinarith

/-- S10-07. The statement of `leaf_count_second` of `SPLIT_prop81.lean`, taken here as the
hypothesis `hleaf` and copied verbatim, implies that there are `c > 0` and `r₀` such that no
primitive real character `χ` of conductor `r ≥ r₀` with `φ(r)² ≥ 8 r` has a real zero `1 - δ`
with `0 < δ < c / log r`: the absence of Landau-Siegel zeros, which is OPEN. The proof is the
argument of P0029 page 32, proof of Theorem 8.2, run with the leaf in place of display 8.4: on
the even multiples of `r` in `[X/2, X]`, `X = 4 r³`, the character term is large by display 8.1,
`char_term_large_S10`, and there are more than `r²` of them, against `C_ε X^(19/30)`. -/
theorem leaf_count_second_forces_no_siegel_S10
    (hleaf : ∀ (ϑ : ℝ), 2 / 5 ≤ ϑ → ϑ < 4 / 9 → ∀ (ε : ℝ), 0 < ε →
      ∃ Cε : ℝ, ∀ (X : ℝ), 2 ≤ X → ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (δ : ℝ),
        χ.IsPrimitive → IsRealChar χ → (r : ℝ) ≤ X ^ ϑ → 0 < δ → δ < (1 / 2) / Real.log X →
        DirichletCharacter.LFunction χ ((1 - δ : ℝ) : ℂ) = 0 →
        (((((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊)).filter (fun N : ℕ => Even N ∧
            ¬ ‖genSing χ χ N * betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ) *
                (N : ℂ) ^ (2 * ((1 - δ : ℝ) : ℂ) - 1)‖ ≤
            (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
                singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
                  X ^ (1 - (1 : ℝ) / 10)) / 2)).card : ℕ) : ℝ) ≤
          Cε * X ^ (3 / 5 + ε)) :
    ∃ c : ℝ, 0 < c ∧ ∃ r₀ : ℕ, ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), r₀ ≤ r →
      χ.IsPrimitive → IsRealChar χ → 8 * (r : ℝ) ≤ (Nat.totient r : ℝ) ^ 2 →
      ∀ δ : ℝ, 0 < δ → δ < c / Real.log r →
        DirichletCharacter.LFunction χ ((1 - δ : ℝ) : ℂ) ≠ 0 := by
  obtain ⟨C, hC⟩ := hleaf (2 / 5) le_rfl (by norm_num) (1 / 30) (by norm_num)
  refine ⟨((1 : ℝ) / 16) ^ 10 / 4, by positivity, max (2 ^ 14) ⌈(4 * |C| + 1) ^ 30⌉₊, ?_⟩
  intro r _ χ hr0 hprim hreal htot δ hδ hδc hL
  have hr14 : 2 ^ 14 ≤ r := le_trans (le_max_left _ _) hr0
  have hrC : ((4 * |C| + 1) ^ 30 : ℝ) ≤ r :=
    Nat.ceil_le.mp (le_trans (le_max_right _ _) hr0)
  have hrR : (2 : ℝ) ^ 14 ≤ r := by exact_mod_cast hr14
  have hr4 : (4 : ℝ) ≤ r := by
    have : (4 : ℝ) ≤ 2 ^ 14 := by norm_num
    linarith
  have hrpos : (0 : ℝ) < r := by linarith
  have hrnat : 0 < r := NeZero.pos r
  set X : ℝ := 4 * (r : ℝ) ^ 3 with hXdef
  have hr3 : ((2 : ℝ) ^ 14) ^ 3 ≤ (r : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hrR 3
  have hXbig : (2 : ℝ) ^ 40 < X := by
    have : ((2 : ℝ) ^ 14) ^ 3 = 2 ^ 42 := by norm_num
    have h2 : (2 : ℝ) ^ 40 < 4 * 2 ^ 42 := by norm_num
    rw [hXdef]
    linarith
  have hXpos : 0 < X := by positivity
  have hX2 : 2 ≤ X := by
    have : (2 : ℝ) ≤ 2 ^ 40 := by norm_num
    linarith
  have hlogr : 0 < Real.log r := Real.log_pos (by linarith)
  have hlogX : Real.log X ≤ 4 * Real.log r := by
    have h1 : Real.log X = Real.log 4 + 3 * Real.log r := by
      rw [hXdef, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    have h2 : Real.log 4 ≤ Real.log r := Real.log_le_log (by norm_num) hr4
    linarith
  have hδr : δ * Real.log r < ((1 : ℝ) / 16) ^ 10 / 4 := (lt_div_iff₀ hlogr).mp hδc
  have hlogX0 : 0 < Real.log X := Real.log_pos (by linarith)
  have hη : δ * Real.log X ≤ ((1 : ℝ) / 16) ^ 10 := by
    have := mul_le_mul_of_nonneg_left hlogX hδ.le
    linarith
  have hδX : δ < (1 / 2) / Real.log X := by
    rw [lt_div_iff₀ hlogX0]
    have : ((1 : ℝ) / 16) ^ 10 < 1 / 2 := by norm_num
    linarith
  have hrϑ : (r : ℝ) ≤ X ^ ((2 : ℝ) / 5) := by
    have hX5 : (X ^ ((2 : ℝ) / 5)) ^ (5 : ℕ) = X ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]
      norm_num
    have hle : (r : ℝ) ^ (5 : ℕ) ≤ (X ^ ((2 : ℝ) / 5)) ^ (5 : ℕ) := by
      rw [hX5, hXdef]
      have h16 : (1 : ℝ) ≤ 16 * r := by linarith
      have h5 : (0 : ℝ) ≤ (r : ℝ) ^ 5 := by positivity
      have := mul_le_mul_of_nonneg_left h16 h5
      nlinarith
    exact (pow_le_pow_iff_left₀ hrpos.le (Real.rpow_nonneg hXpos.le _) (by norm_num)).mp hle
  have hcount := hC X hX2 r χ δ hprim hreal hrϑ hδ hδX hL
  rw [show (3 : ℝ) / 5 + 1 / 30 = 19 / 30 by norm_num] at hcount
  refine (not_lt.mpr hcount) ?_
  refine lt_of_lt_of_le (b := ((((Finset.Icc (r ^ 2) (2 * r ^ 2)).image
      (fun k : ℕ => 2 * r * k)).card : ℕ) : ℝ)) ?_ (Nat.cast_le.mpr (Finset.card_le_card ?_))
  · -- the numerics
    have hinj : Function.Injective (fun k : ℕ => 2 * r * k) := by
      intro a b h
      exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 * r) h
    rw [Finset.card_image_of_injective _ hinj, Nat.card_Icc]
    have hc : 2 * r ^ 2 + 1 - r ^ 2 = r ^ 2 + 1 := by
      generalize r ^ 2 = m
      omega
    rw [hc]
    push_cast
    have hA : 0 < X ^ ((19 : ℝ) / 30) := Real.rpow_pos_of_pos hXpos _
    have hB : 4 * |C| + 1 ≤ X ^ ((1 : ℝ) / 30) := by
      have hXr : (r : ℝ) ≤ X := by
        rw [hXdef]
        have : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
        nlinarith
      have h0 : (0 : ℝ) ≤ (4 * |C| + 1) ^ (30 : ℕ) := by positivity
      have h1 := Real.rpow_le_rpow h0 (hrC.trans hXr) (by norm_num : (0 : ℝ) ≤ 1 / 30)
      have h2 : ((4 * |C| + 1) ^ (30 : ℕ)) ^ (((30 : ℕ) : ℝ)⁻¹) = 4 * |C| + 1 :=
        Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
      rw [show ((1 : ℝ) / 30) = ((30 : ℕ) : ℝ)⁻¹ by norm_num, h2] at h1
      rw [show ((1 : ℝ) / 30) = ((30 : ℕ) : ℝ)⁻¹ by norm_num]
      exact h1
    have hsplit : X ^ ((2 : ℝ) / 3) = X ^ ((19 : ℝ) / 30) * X ^ ((1 : ℝ) / 30) := by
      rw [← Real.rpow_add hXpos]
      norm_num
    have h23 : X ^ ((2 : ℝ) / 3) ≤ 4 * (r : ℝ) ^ 2 := by
      have hX3 : (X ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) = X ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]
        norm_num
      have hle : (X ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) ≤ (4 * (r : ℝ) ^ 2) ^ (3 : ℕ) := by
        rw [hX3, hXdef]
        have h6 : (0 : ℝ) ≤ (r : ℝ) ^ 6 := by positivity
        nlinarith
      exact (pow_le_pow_iff_left₀ (Real.rpow_nonneg hXpos.le _) (by positivity)
        (by norm_num)).mp hle
    have hm := mul_le_mul_of_nonneg_left hB hA.le
    have hCabs : C * X ^ ((19 : ℝ) / 30) ≤ |C| * X ^ ((19 : ℝ) / 30) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hA.le
    nlinarith
  · -- every `2 r k`, `r² ≤ k ≤ 2 r²`, is in the counted set
    intro N hN
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hN
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    have hk1' : (r : ℝ) ^ 2 ≤ k := by exact_mod_cast hk1
    have hk2' : (k : ℝ) ≤ 2 * (r : ℝ) ^ 2 := by exact_mod_cast hk2
    have hNcast : ((2 * r * k : ℕ) : ℝ) = 2 * (r : ℝ) * k := by push_cast; ring
    have hlo : X / 2 ≤ ((2 * r * k : ℕ) : ℝ) := by
      rw [hNcast, hXdef]
      nlinarith
    have hhi : ((2 * r * k : ℕ) : ℝ) ≤ X := by
      rw [hNcast, hXdef]
      nlinarith
    have hEven : Even (2 * r * k) := ⟨r * k, by ring⟩
    have hdvd : r ∣ 2 * r * k := ⟨2 * k, by ring⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.ceil_le.mpr hlo, Nat.le_floor hhi⟩, hEven, ?_⟩
    exact char_term_large_S10 r χ hprim hreal htot X δ hXbig hδ hη (2 * r * k) hEven hdvd hlo hhi

/-- Faithfulness check, not a result: the hypothesis `hleaf` of
`leaf_count_second_forces_no_siegel_S10` is exactly the statement of `leaf_count_second`, so the
open leaf can be plugged in. This example depends on the open leaf and is not counted as proved. -/
example : True := by
  have _h := leaf_count_second_forces_no_siegel_S10
    (fun ϑ h1 h2 ε hε => leaf_count_second ϑ h1 h2 ε hε)
  trivial

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.leaf_count_second_forces_no_siegel_S10
#print axioms LeanLab.BhowmikGrimmelt2026.char_term_large_S10
#print axioms LeanLab.BhowmikGrimmelt2026.prime_totient_sq_S10
