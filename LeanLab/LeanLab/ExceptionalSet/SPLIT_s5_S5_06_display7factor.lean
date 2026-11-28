import LeanLab.ExceptionalSet.SPLIT_feed1122p2_leaf_karW_display7

/-!
Split of `leaf_karW_display7_factor` of
`LeanLab.ExceptionalSet.SPLIT_feed1122p2_leaf_karW_display7`, burst-20261127, CLOUD S5 unit S5-06.
A. A. Karacuba, Trudy Mat. Inst. Steklov 112 (1971), p. 246 display (6) and p. 247, the estimate
of `𝔖_s` for `s = s_1, ..., s_r` and display (7).

Notation. `B_s = f^{(s)}(a)/s!`, `M = P2 = karP2 c1 n P`, `K = kM^s`, `Q_s = [|B_s|^{-1}]`,
`X = (M+1)^s`, `ρ = min(c1/3, c3, c4)`.

Pieces.
* `karMinGeom`, the summand `min(2K+1, 1/(2‖θ‖))` of display (6) with the paper's convention
  that it is `2K+1` when `θ` is an integer.
* `leaf_karW_geom_bound`, proved: `|Σ_{|t| ≤ K} e(θt)| ≤ 1/(2‖θ‖)` for `‖θ‖ > 0`, from
  `karW_eC_nat_mul` and `karW_eC_sub_one_ge`, `|e(θ) - 1| ≥ 4‖θ‖`.
* `karW_geom_min`, proved from it and the trivial bound: `|Σ_{|t| ≤ K} e(θt)| ≤ karMinGeom K θ`.
* `leaf_karW_lemma3_applied`, proved by CLOUD S5-06c from `karacuba_lemma3_regularized`: Lemma 3 on the sum over `|μ| ≤ K`,
  `Σ_μ min(2K+1, 1/(2‖B μ‖)) ≤ 6(2K+1+Q log Q)((2K+1)Q^{-1}+1)`.
* `leaf_karW_display7_arith`, proved: `6(2K+1+Q log Q)((2K+1)Q^{-1}+1) ≤ 108k²X²(Q^{-1}+X^{-1}log Q+X^{-2}Q log Q)`.
* `leaf_karW_display7_Qbounds`, proved by CLOUD S5-06b with `cc0 = max(1, 1/c3)`: `Q^{-1}+X^{-1}log Q+X^{-2}Q log Q ≤ 9n P^{-ρs} log P`.
* `leaf_karW_display7_factor_of_leaves`, the exact statement of `leaf_karW_display7_factor`, proved.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-- The summand of display (6), Karacuba p. 246: `min(2K+1, 1/(2‖θ‖))`, which the paper takes to
be `2K+1` when `θ` is an integer. -/
noncomputable def karMinGeom (K : ℕ) (θ : ℝ) : ℝ :=
  if nint θ = 0 then ((2 * K + 1 : ℕ) : ℝ) else min ((2 * K + 1 : ℕ) : ℝ) (1 / (2 * nint θ))

/-- `e(θ m) = e(θ)^m`. -/
theorem karW_eC_nat_mul (θ : ℝ) (m : ℕ) : eC (θ * (m : ℝ)) = eC θ ^ m := by
  unfold eC
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `|e(θ) - 1| ≥ 4‖θ‖`, from `|e(θ) - 1| = 2|sin πθ|` and `|sin πθ| ≥ 2‖θ‖`. -/
theorem karW_eC_sub_one_ge (θ : ℝ) : 4 * nint θ ≤ ‖eC θ - 1‖ := by
  have h1 : eC θ = Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)) := by
    unfold eC
    congr 1
    push_cast
    ring
  rw [h1, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_two]
  have h2 : 2 * Real.pi * θ / 2 = Real.pi * Int.fract θ + (⌊θ⌋ : ℝ) * Real.pi := by
    have := Int.floor_add_fract θ
    nth_rewrite 1 [← this]
    ring
  rw [h2, Real.sin_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
  set f := Int.fract θ with hf
  have hf0 : 0 ≤ f := Int.fract_nonneg θ
  have hf1 : f < 1 := Int.fract_lt_one θ
  have hn : nint θ = min f (1 - f) := rfl
  have hsin0 : 0 ≤ Real.sin (Real.pi * f) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
  rw [abs_of_nonneg hsin0]
  have hn0 : 0 ≤ nint θ := by rw [hn]; exact le_min hf0 (by linarith)
  have hn12 : nint θ ≤ 1 / 2 := by
    rw [hn]
    rcases le_total f (1 / 2) with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (by linarith)
  have hsn : Real.sin (Real.pi * f) = Real.sin (Real.pi * nint θ) := by
    rw [hn]
    rcases le_total f (1 - f) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, mul_sub, mul_one, Real.sin_pi_sub]
  rw [hsn]
  have := Real.mul_le_sin (x := Real.pi * nint θ) (by positivity) (by nlinarith [Real.pi_pos])
  have hp : 2 / Real.pi * (Real.pi * nint θ) = 2 * nint θ := by
    field_simp
  linarith

/-- The finite geometric sum bound behind display (6), Karacuba p. 246:
for `‖θ‖ > 0`, `|Σ_{|t| ≤ K} e(θ t)| ≤ 1/(2‖θ‖)`. -/
theorem leaf_karW_geom_bound (K : ℕ) (θ : ℝ) (hθ : 0 < nint θ) :
    ‖∑ t ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), eC (θ * (t : ℝ))‖ ≤ 1 / (2 * nint θ) := by
  have hI : Finset.Icc (-(K : ℤ)) (K : ℤ) = (Finset.range (2 * K + 1)).map
      ⟨fun m : ℕ => (m : ℤ) - K, fun a b h => by simpa using h⟩ := by
    ext t
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(t + K).toNat, by omega, ?_⟩
      show (((t + K).toNat : ℕ) : ℤ) - K = t
      omega
    · rintro ⟨m, hm, rfl⟩
      show -(K : ℤ) ≤ (m : ℤ) - K ∧ (m : ℤ) - K ≤ K
      omega
  set w := eC θ with hw
  have hS : ∑ t ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), eC (θ * (t : ℝ))
      = eC (-(θ * K)) * ∑ m ∈ Finset.range (2 * K + 1), w ^ m := by
    rw [hI, Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    show eC (θ * ((((m : ℤ) - K : ℤ)) : ℝ)) = eC (-(θ * K)) * w ^ m
    rw [hw, ← karW_eC_nat_mul, ← karW_eC_add]
    congr 1
    push_cast
    ring
  have hw1 : 4 * nint θ ≤ ‖w - 1‖ := karW_eC_sub_one_ge θ
  have hpos : 0 < ‖w - 1‖ := lt_of_lt_of_le (by linarith) hw1
  have hgeom : ‖∑ m ∈ Finset.range (2 * K + 1), w ^ m‖ * ‖w - 1‖ ≤ 2 := by
    rw [← norm_mul, geom_sum_mul]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, hw, karW_eC_norm, one_pow, norm_one]
    norm_num
  rw [hS, norm_mul, karW_eC_norm, one_mul]
  have h2 : ‖∑ m ∈ Finset.range (2 * K + 1), w ^ m‖ ≤ 2 / ‖w - 1‖ := by
    rw [le_div_iff₀ hpos]; exact hgeom
  refine h2.trans ?_
  rw [show 1 / (2 * nint θ) = 2 / (4 * nint θ) by field_simp; ring]
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith) hw1

/-- Display (6) per term, Karacuba p. 246: `|Σ_{|t| ≤ K} e(θ t)| ≤ min(2K+1, 1/(2‖θ‖))`. -/
theorem karW_geom_min (K : ℕ) (θ : ℝ) :
    ‖∑ t ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), eC (θ * (t : ℝ))‖ ≤ karMinGeom K θ := by
  have htriv : ‖∑ t ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), eC (θ * (t : ℝ))‖
      ≤ ((2 * K + 1 : ℕ) : ℝ) := by
    have hcard : ((Finset.Icc (-(K : ℤ)) (K : ℤ)).card : ℝ) = ((2 * K + 1 : ℕ) : ℝ) := by
      rw [Int.card_Icc]
      congr 1
      omega
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp only [karW_eC_norm, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact hcard
  unfold karMinGeom
  split_ifs with h0
  · exact htriv
  · have hpos : 0 < nint θ := by
      have : 0 ≤ nint θ := by
        unfold nint
        exact le_min (Int.fract_nonneg _) (by linarith [Int.fract_lt_one θ])
      exact lt_of_le_of_ne this (Ne.symm h0)
    exact le_min htriv (leaf_karW_geom_bound K θ hpos)

/-- Lemma 3 of Karacuba p. 244 applied on p. 247 to `𝔖_s`, proved from
`Decomp538a.karacuba_lemma3_regularized`. For real `B`
with `0 < |B| ≤ 1` and `Q = [|B|^{-1}] ≥ 1`, write `B = ±(1/Q + θ/Q²)` with `|θ| ≤ 1`; Lemma 3
with `U = 2K+1`, `2K+1` consecutive `μ` and the paper's convention `1/0 = ∞` gives
`Σ_{|μ| ≤ K} min(2K+1, 1/(2‖Bμ‖)) ≤ 6(2K+1+Q log Q)((2K+1)Q^{-1}+1)`. The lab's `KarLemma3`
drops the integer points, where `1/0 = 0` in Lean, so it does not give this alone; the
regularized form of Decomp538a does. -/
theorem leaf_karW_lemma3_applied (B : ℝ) (K : ℕ) (hB0 : 0 < |B|) (hB1 : |B| ≤ 1) :
    ∑ μ ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), karMinGeom K (B * (μ : ℝ))
      ≤ 6 * (((2 * K + 1 : ℕ) : ℝ) + (⌊|B|⁻¹⌋₊ : ℝ) * Real.log (⌊|B|⁻¹⌋₊ : ℝ)) *
        (((2 * K + 1 : ℕ) : ℝ) / (⌊|B|⁻¹⌋₊ : ℝ) + 1) := by
  set q : ℕ := ⌊|B|⁻¹⌋₊ with hqdef
  set U : ℝ := ((2 * K + 1 : ℕ) : ℝ) with hU
  have hinv1 : (1 : ℝ) ≤ |B|⁻¹ := by rw [one_le_inv₀ hB0]; exact hB1
  have hq1 : 1 ≤ q := Nat.le_floor (by exact_mod_cast hinv1)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqle : (q : ℝ) ≤ |B|⁻¹ := Nat.floor_le (by positivity)
  have hqlt : |B|⁻¹ < (q : ℝ) + 1 := Nat.lt_floor_add_one _
  have hqB : (q : ℝ) * |B| ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hqle hB0.le
    rwa [inv_mul_cancel₀ hB0.ne'] at this
  have hqB2 : 1 < ((q : ℝ) + 1) * |B| := by
    have := mul_lt_mul_of_pos_right hqlt hB0
    rwa [inv_mul_cancel₀ hB0.ne'] at this
  -- `B = a/q + θ/q²` with `a = ±1`, `|θ| ≤ 1`
  set a : ℤ := if 0 < B then 1 else -1 with ha
  set θ : ℝ := (B - (a : ℝ) / q) * (q : ℝ) ^ 2 with hθ
  have hq0 : (0 : ℝ) < q := by linarith
  have hBeq : (a : ℝ) / q + θ / (q : ℝ) ^ 2 = B := by
    rw [hθ]; field_simp; ring
  have hgcd : Int.gcd a q = 1 := by
    rw [ha]; split_ifs <;> simp
  have hθ1 : |θ| ≤ 1 := by
    have hkey : |B - (a : ℝ) / q| = 1 / q - |B| := by
      rw [ha]
      split_ifs with hBp
      · rw [abs_of_pos hBp]
        push_cast
        rw [abs_sub_comm, abs_of_nonneg]
        rw [abs_of_pos hBp] at hqB
        rw [sub_nonneg, le_div_iff₀ hq0]; linarith
      · have hBn : B < 0 := by
          rcases lt_or_eq_of_le (not_lt.mp hBp) with h | h
          · exact h
          · rw [h, abs_zero] at hB0; exact absurd hB0 (lt_irrefl 0)
        rw [abs_of_neg hBn]
        push_cast
        rw [show B - -1 / (q : ℝ) = -(-B - 1 / q) by ring, abs_neg, abs_sub_comm, abs_of_nonneg]
        rw [abs_of_neg hBn] at hqB
        rw [sub_nonneg, le_div_iff₀ hq0]; linarith
    rw [hθ, abs_mul, hkey, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ 2)]
    have e : (1 / (q : ℝ) - |B|) * (q : ℝ) ^ 2 = q - (q : ℝ) ^ 2 * |B| := by
      field_simp
    rw [e]
    nlinarith
  -- reindex `μ = x - (K + 1)`, `x ∈ [1, 2K+1]`
  have hI : Finset.Icc (-(K : ℤ)) (K : ℤ) = (Finset.Icc 1 (2 * K + 1)).map
      ⟨fun x : ℕ => (x : ℤ) - (K + 1), fun x y h => by simpa using h⟩ := by
    ext t
    simp only [Finset.mem_Icc, Finset.mem_map]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(t + K + 1).toNat, by omega, ?_⟩
      show (((t + K + 1).toNat : ℕ) : ℤ) - (K + 1) = t
      omega
    · rintro ⟨m, hm, rfl⟩
      show -(K : ℤ) ≤ (m : ℤ) - (K + 1) ∧ (m : ℤ) - (K + 1) ≤ K
      omega
  set β : ℝ := -(B * ((K : ℝ) + 1)) with hβ
  have hsum : ∑ μ ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), karMinGeom K (B * (μ : ℝ))
      = ∑ x ∈ Finset.Icc 1 (2 * K + 1), karMinGeom K ((a / q + θ / (q : ℝ) ^ 2) * x + β) := by
    rw [hI, Finset.sum_map]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    show karMinGeom K (B * ((((x : ℤ) - (K + 1) : ℤ)) : ℝ)) = _
    rw [hBeq, hβ]
    congr 1
    push_cast
    ring
  rw [hsum]
  have hle : ∀ y : ℝ, karMinGeom K y ≤
      (if Int.fract y = 0 then U else min U (1 / min (Int.fract y) (1 - Int.fract y))) := by
    intro y
    unfold karMinGeom
    have hn : nint y = min (Int.fract y) (1 - Int.fract y) := rfl
    have h1f : 0 < 1 - Int.fract y := by linarith [Int.fract_lt_one y]
    by_cases hf : Int.fract y = 0
    · have : nint y = 0 := by rw [hn, hf]; simp
      rw [if_pos this, if_pos hf]
    · have hpos : 0 < nint y := by
        rw [hn]
        exact lt_min (lt_of_le_of_ne (Int.fract_nonneg y) (Ne.symm hf)) h1f
      rw [if_neg hpos.ne', if_neg hf, ← hn]
      apply min_le_min_left
      apply one_div_le_one_div_of_le hpos
      linarith
  refine (Finset.sum_le_sum (fun x _ => hle _)).trans ?_
  have hUpos : 0 < U := by rw [hU]; positivity
  have h := LeanLab.ExceptionalSet.Decomp538a.karacuba_lemma3_regularized U (2 * K + 1) a q θ β
    hUpos hq1 hgcd hθ1
  exact h

/-- The arithmetic of p. 247, `6(2kP2^s+1+Q log Q)((2kP2^s+1)Q^{-1}+1) ≤
30k²P2^{2s}(Q^{-1}+P2^{-s}log Q+P2^{-2s}Q log Q)`, class EASY, with `X = (P2+1)^s` in place of
`P2^s` and the constant `108` in place of the paper's `30`, proved: with `2K+1 ≤ 3kX`, the cross term
`18kX` is at most `54k²X²/Q` when `Q ≤ 3` and at most `18kX log Q` when `Q > 3`. -/
theorem leaf_karW_display7_arith (k : ℕ) (X K Q : ℝ) (hk : 1 ≤ k) (hX : 1 ≤ X) (hK0 : 0 ≤ K)
    (hK : K ≤ k * X) (hQ : 1 ≤ Q) :
    6 * ((2 * K + 1) + Q * Real.log Q) * ((2 * K + 1) / Q + 1)
      ≤ 108 * (k : ℝ) ^ 2 * X ^ 2 * (Q⁻¹ + X⁻¹ * Real.log Q + (X ^ 2)⁻¹ * Q * Real.log Q) := by
  have hQ0 : 0 < Q := by linarith
  have hX0 : 0 < X := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set L := Real.log Q with hLdef
  have hL : 0 ≤ L := Real.log_nonneg hQ
  set A : ℝ := 2 * K + 1 with hAdef
  have hA0 : 0 ≤ A := by linarith
  have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hkX1 : (1 : ℝ) ≤ k * X := one_le_mul_of_one_le_of_one_le hk1 hX
  have hkX : (k : ℝ) * X ≤ (k : ℝ) ^ 2 * X ^ 2 := by nlinarith
  have hkX2 : (k : ℝ) * X ≤ (k : ℝ) ^ 2 * X := mul_le_mul_of_nonneg_right hkk hX0.le
  have hA : A ≤ 3 * k * X := by nlinarith
  have eR : 108 * (k : ℝ) ^ 2 * X ^ 2 * (Q⁻¹ + X⁻¹ * L + (X ^ 2)⁻¹ * Q * L)
      = 108 * ((k : ℝ) ^ 2 * X ^ 2 / Q) + 108 * ((k : ℝ) ^ 2 * X * L) + 108 * ((k : ℝ) ^ 2 * Q * L) := by
    field_simp
  have eL : 6 * (A + Q * L) * (A / Q + 1) = 6 * (A ^ 2 / Q) + 6 * A + 6 * (A * L) + 6 * (Q * L) := by
    field_simp; ring
  rw [eR, eL]
  have h1 : A ^ 2 / Q ≤ 9 * ((k : ℝ) ^ 2 * X ^ 2 / Q) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hQ0.le
    nlinarith
  have h2 : A ≤ 9 * ((k : ℝ) ^ 2 * X ^ 2 / Q) + 15 * ((k : ℝ) ^ 2 * X * L) := by
    have hp : 0 ≤ (k : ℝ) ^ 2 * X * L := by positivity
    rcases le_or_gt Q 3 with hQ3 | hQ3
    · have : (k : ℝ) ^ 2 * X ^ 2 / 3 ≤ (k : ℝ) ^ 2 * X ^ 2 / Q :=
        div_le_div_of_nonneg_left (by positivity) hQ0 hQ3
      nlinarith
    · have hL1 : 1 ≤ L := by
        rw [hLdef, Real.le_log_iff_exp_le hQ0]
        have := Real.exp_one_lt_d9
        linarith
      have : (k : ℝ) * X ≤ (k : ℝ) ^ 2 * X * L := by
        have h0 : 0 ≤ (k : ℝ) ^ 2 * X := by positivity
        nlinarith
      have : 0 ≤ (k : ℝ) ^ 2 * X ^ 2 / Q := by positivity
      nlinarith
  have h3 : A * L ≤ 3 * ((k : ℝ) ^ 2 * X * L) := by
    have : A ≤ 3 * ((k : ℝ) ^ 2 * X) := by linarith
    have := mul_le_mul_of_nonneg_right this hL
    linarith
  have h4 : Q * L ≤ (k : ℝ) ^ 2 * Q * L := by
    have : 0 ≤ Q * L := by positivity
    nlinarith
  nlinarith

/-- From `n ≥ karN0 c1 c2 c4`: `1/(n²(n+1)) ≤ c1 - c2 - c4` and `1/(n²(n+1)) ≤ c1/3`. -/
theorem karN0_delta (c1 c2 c4 : ℝ) (n : ℕ) (hc1 : 0 < c1) (hc241 : c2 + c4 < c1)
    (hn0 : karN0 c1 c2 c4 ≤ n) :
    1 / ((n : ℝ) ^ 2 * (n + 1)) ≤ c1 - (c2 + c4) ∧ 1 / ((n : ℝ) ^ 2 * (n + 1)) ≤ c1 / 3 := by
  unfold karN0 at hn0
  have h12 : (12 : ℝ) ≤ n := le_trans (le_max_left _ _) hn0
  have hA : 1 / Real.sqrt c1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn0
  have hB : 1 / (c1 - (c2 + c4)) ^ ((1 : ℝ) / 3) ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn0
  have hd : 0 < c1 - (c2 + c4) := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hden : 0 < (n : ℝ) ^ 2 * (n + 1) := by positivity
  constructor
  · -- `n³ ≥ 1/d`
    have hcube : 0 < (c1 - (c2 + c4)) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hd _
    have h1 : 1 ≤ (n : ℝ) * (c1 - (c2 + c4)) ^ ((1 : ℝ) / 3) := by
      rw [div_le_iff₀ hcube] at hB; linarith
    have h3 : 1 ≤ ((n : ℝ) * (c1 - (c2 + c4)) ^ ((1 : ℝ) / 3)) ^ 3 := one_le_pow₀ h1
    have h4 : ((n : ℝ) * (c1 - (c2 + c4)) ^ ((1 : ℝ) / 3)) ^ 3 = (n : ℝ) ^ 3 * (c1 - (c2 + c4)) := by
      rw [mul_pow, ← Real.rpow_natCast ((c1 - (c2 + c4)) ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul hd.le]
      norm_num
    rw [h4] at h3
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg (n : ℝ)]
  · have hs : 0 < Real.sqrt c1 := Real.sqrt_pos.mpr hc1
    have h1 : 1 ≤ (n : ℝ) * Real.sqrt c1 := by
      rw [div_le_iff₀ hs] at hA; linarith
    have h2 : 1 ≤ ((n : ℝ) * Real.sqrt c1) ^ 2 := one_le_pow₀ h1
    rw [mul_pow, Real.sq_sqrt hc1.le] at h2
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg (n : ℝ)]

set_option maxHeartbeats 1000000 in
/-- The bounds of p. 247 from the definitions of `Q_s` and `P2`, proved:
`Q_s^{-1} ≤ 2P^{-c3 s}`, `P2^{-1} ≤ 2P^{-c1/3}`, `P2^{-2s}Q_s ≤ 2P^{-c4 s}`, `log Q_s ≤ n log P`,
hence `Q_s^{-1} + P2^{-s} log Q_s + P2^{-2s} Q_s log Q_s ≤ 9n P^{-ρ s} log P`, here with `P2 + 1`
in place of `P2`. Uses `P^{-c2 s} ≤ |B_s| ≤ P^{-c3 s}` from `KarHyp`, `n ≥ karN0` and `P` large. -/
theorem leaf_karW_display7_Qbounds :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ cc0 : ℝ, 0 < cc0 ∧
        ∀ (N P n : ℕ) (f : ℝ → ℝ) (T : Finset ℕ) (a k : ℕ), 0 < P → 2 ≤ n →
          karN0 c1 c2 c4 ≤ n → Real.exp (cc0 * (n : ℝ) ^ 2) ≤ P →
          KarHyp c0 c1 c2 c3 N P n f T → N ≤ a → a + karP2 c1 n P ^ 2 ≤ N + P →
          n * (n + 1) ≤ 4 * k → ∀ s ∈ T,
            ((⌊|iteratedDeriv s f (a : ℝ) / (s.factorial : ℝ)|⁻¹⌋₊ : ℕ) : ℝ)⁻¹
              + (((karP2 c1 n P : ℝ) + 1) ^ s)⁻¹ *
                Real.log (⌊|iteratedDeriv s f (a : ℝ) / (s.factorial : ℝ)|⁻¹⌋₊ : ℝ)
              + ((((karP2 c1 n P : ℝ) + 1) ^ s) ^ 2)⁻¹ *
                (⌊|iteratedDeriv s f (a : ℝ) / (s.factorial : ℝ)|⁻¹⌋₊ : ℝ) *
                Real.log (⌊|iteratedDeriv s f (a : ℝ) / (s.factorial : ℝ)|⁻¹⌋₊ : ℝ)
            ≤ 9 * (n : ℝ) * (P : ℝ) ^ (-(min (c1 / 3) (min c3 c4) * (s : ℝ))) *
                Real.log (P : ℝ) := by
  intro c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 hc241
  refine ⟨max 1 (1 / c3), by positivity, ?_⟩
  intro N P n f T a k hP hn hn0 hbig hH ha haP hnk s hs
  set b : ℝ := iteratedDeriv s f (a : ℝ) / (s.factorial : ℝ) with hb
  set B : ℝ := |b| with hBdef
  set Q : ℝ := ((⌊B⁻¹⌋₊ : ℕ) : ℝ) with hQdef
  set M : ℕ := karP2 c1 n P with hM
  set X : ℝ := ((M : ℝ) + 1) ^ s with hX
  set L : ℝ := Real.log (P : ℝ) with hLdef
  set ρ : ℝ := min (c1 / 3) (min c3 c4) with hρ
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsT : s ∈ Finset.Icc 2 n := hH.2.2.1 hs
  rw [Finset.mem_Icc] at hsT
  have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast hsT.1
  have hsn : (s : ℝ) ≤ n := by exact_mod_cast hsT.2
  have hL : max 1 (1 / c3) * (n : ℝ) ^ 2 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hP0]; exact hbig
  have hL1 : 1 ≤ L := by
    have : (1 : ℝ) ≤ max 1 (1 / c3) := le_max_left _ _
    nlinarith
  have hL0 : 0 ≤ L := by linarith
  have hc3L : 1 ≤ c3 * s * L := by
    have h1 : (1 / c3) * (n : ℝ) ^ 2 ≤ L :=
      le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) hL
    have h2 : 1 ≤ c3 * L := by
      have := mul_le_mul_of_nonneg_left h1 hc3.le
      rw [← mul_assoc, mul_one_div_cancel hc3.ne', one_mul] at this
      nlinarith
    nlinarith
  -- `P^x = exp(x log P)`
  have hrp : ∀ x : ℝ, (P : ℝ) ^ x = Real.exp (L * x) := fun x => by
    rw [Real.rpow_def_of_pos hP0]
  -- the bounds on `B`
  have haI : (a : ℝ) ∈ Set.Icc (N : ℝ) (N + P) := by
    constructor
    · exact_mod_cast ha
    · have : a ≤ N + P := by
        have := Nat.zero_le (karP2 c1 n P ^ 2); omega
      exact_mod_cast this
  have hbB := hH.2.2.2.2 s hs (a : ℝ) haI
  have hB0 : 0 < B := lt_of_lt_of_le (Real.rpow_pos_of_pos hP0 _) hbB.1
  have hBinv_lo : (P : ℝ) ^ (c3 * s) ≤ B⁻¹ := by
    have := hbB.2
    rw [← inv_le_inv₀ (Real.rpow_pos_of_pos hP0 _) hB0, ← Real.rpow_neg hP0.le] at this
    simpa [neg_mul] using this
  have hBinv_hi : B⁻¹ ≤ (P : ℝ) ^ (c2 * s) := by
    have := hbB.1
    rw [← inv_le_inv₀ hB0 (Real.rpow_pos_of_pos hP0 _), ← Real.rpow_neg hP0.le] at this
    simpa [neg_mul] using this
  have hPc3 : 2 ≤ (P : ℝ) ^ (c3 * s) := by
    rw [hrp]
    have : Real.exp 1 ≤ Real.exp (L * (c3 * s)) := Real.exp_le_exp.2 (by nlinarith)
    have h2 := Real.exp_one_gt_d9
    linarith
  have hQhi : Q ≤ B⁻¹ := Nat.floor_le (by positivity)
  have hQlo : B⁻¹ - 1 < Q := by
    have := Nat.lt_floor_add_one B⁻¹
    rw [hQdef]; linarith
  have hQ1 : 1 ≤ Q := by
    rw [hQdef]
    exact_mod_cast Nat.le_floor (by push_cast; linarith)
  have hQ0 : 0 < Q := by linarith
  -- the three terms
  have hT1 : Q⁻¹ ≤ 2 * (P : ℝ) ^ (-(c3 * s)) := by
    rw [Real.rpow_neg hP0.le]
    have hp : 0 < (P : ℝ) ^ (c3 * s) := Real.rpow_pos_of_pos hP0 _
    rw [inv_le_iff_one_le_mul₀ hQ0]
    have : (P : ℝ) ^ (c3 * s) ≤ 2 * Q := by linarith
    calc (1 : ℝ) = ((P : ℝ) ^ (c3 * s))⁻¹ * (P : ℝ) ^ (c3 * s) := by field_simp
      _ ≤ ((P : ℝ) ^ (c3 * s))⁻¹ * (2 * Q) := by gcongr
      _ = 2 * ((P : ℝ) ^ (c3 * s))⁻¹ * Q := by ring
  have hlogQ0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hlogQ : Real.log Q ≤ n * L := by
    have h1 : Real.log Q ≤ Real.log ((P : ℝ) ^ (c2 * s)) :=
      Real.log_le_log hQ0 (hQhi.trans hBinv_hi)
    rw [Real.log_rpow hP0] at h1
    have hc2_1 : c2 < 1 := by linarith
    have : c2 * s ≤ n := by nlinarith
    nlinarith
  obtain ⟨hδ1, hδ2⟩ := karN0_delta c1 c2 c4 n hc1 hc241 hn0
  set δ : ℝ := 1 / ((n : ℝ) ^ 2 * (n + 1)) with hδ
  set e : ℝ := c1 / 2 - 1 / (2 * ((n : ℝ) ^ 2 * (n + 1))) with he
  have heδ : e = c1 / 2 - δ / 2 := by rw [he, hδ]; field_simp
  have hP2 : (P : ℝ) ^ e ≤ (M : ℝ) + 1 := by
    have := Nat.lt_floor_add_one ((P : ℝ) ^ e)
    have hk : ((M : ℕ) : ℝ) = ((⌊(P : ℝ) ^ e⌋₊ : ℕ) : ℝ) := rfl
    rw [hk]; linarith
  have hXlo : (P : ℝ) ^ (e * s) ≤ X := by
    rw [Real.rpow_mul hP0.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hP0.le _) hP2 s
  have hXpos : 0 < (P : ℝ) ^ (e * s) := Real.rpow_pos_of_pos hP0 _
  have hX0 : 0 < X := lt_of_lt_of_le hXpos hXlo
  have hT2 : X⁻¹ ≤ (P : ℝ) ^ (-(c1 / 3 * s)) := by
    rw [Real.rpow_neg hP0.le]
    refine inv_anti₀ (Real.rpow_pos_of_pos hP0 _) (le_trans ?_ hXlo)
    apply Real.rpow_le_rpow_of_exponent_le hP1
    have : c1 / 3 ≤ e := by rw [heδ]; linarith
    nlinarith
  have hT3 : (X ^ 2)⁻¹ * Q ≤ (P : ℝ) ^ (-(c4 * s)) := by
    have hX2 : (P : ℝ) ^ (2 * e * s) ≤ X ^ 2 := by
      have : (P : ℝ) ^ (2 * e * s) = ((P : ℝ) ^ (e * s)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le]; ring_nf
      rw [this]; exact pow_le_pow_left₀ hXpos.le hXlo 2
    have hQP : Q ≤ (P : ℝ) ^ (c2 * s) := hQhi.trans hBinv_hi
    calc (X ^ 2)⁻¹ * Q ≤ ((P : ℝ) ^ (2 * e * s))⁻¹ * (P : ℝ) ^ (c2 * s) := by
          gcongr
      _ = (P : ℝ) ^ (c2 * s - 2 * e * s) := by
          rw [Real.rpow_sub hP0, div_eq_inv_mul]
      _ ≤ (P : ℝ) ^ (-(c4 * s)) := by
          apply Real.rpow_le_rpow_of_exponent_le hP1
          have : c2 + c4 ≤ 2 * e := by rw [heδ]; linarith
          nlinarith
  -- every `P^{-x s}` with `x ≥ ρ` is at most `P^{-ρ s}`
  have hmono : ∀ x : ℝ, ρ ≤ x → (P : ℝ) ^ (-(x * s)) ≤ (P : ℝ) ^ (-(ρ * s)) := by
    intro x hx
    apply Real.rpow_le_rpow_of_exponent_le hP1
    nlinarith
  have hρ1 : ρ ≤ c1 / 3 := min_le_left _ _
  have hρ3 : ρ ≤ c3 := (min_le_right _ _).trans (min_le_left _ _)
  have hρ4 : ρ ≤ c4 := (min_le_right _ _).trans (min_le_right _ _)
  have hR0 : 0 ≤ (P : ℝ) ^ (-(ρ * s)) := Real.rpow_nonneg hP0.le _
  have e1 := (hT1.trans (by linarith [hmono c3 hρ3] : 2 * (P : ℝ) ^ (-(c3 * s)) ≤ 2 * (P : ℝ) ^ (-(ρ * s))))
  have e2 : X⁻¹ * Real.log Q ≤ (P : ℝ) ^ (-(ρ * s)) * (n * L) :=
    mul_le_mul ((hT2.trans (hmono _ hρ1))) hlogQ hlogQ0 hR0
  have e3 : (X ^ 2)⁻¹ * Q * Real.log Q ≤ (P : ℝ) ^ (-(ρ * s)) * (n * L) :=
    mul_le_mul ((hT3.trans (hmono _ hρ4))) hlogQ hlogQ0 hR0
  have hnL : 1 ≤ (n : ℝ) * L := by nlinarith
  nlinarith

/-- The exact statement of `leaf_karW_display7_factor`, from the pieces. -/
theorem leaf_karW_display7_factor_of_leaves (h3 : KarLemma3) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ cc0 : ℝ, 0 < cc0 ∧
        ∀ (N P n : ℕ) (f : ℝ → ℝ) (T : Finset ℕ) (a k : ℕ), 0 < P → 2 ≤ n →
          karN0 c1 c2 c4 ≤ n → Real.exp (cc0 * (n : ℝ) ^ 2) ≤ P →
          KarHyp c0 c1 c2 c3 N P n f T → N ≤ a → a + karP2 c1 n P ^ 2 ≤ N + P →
          n * (n + 1) ≤ 4 * k → ∀ s ∈ T,
              ∑ μ ∈ Finset.Icc (-((k * karP2 c1 n P ^ s : ℕ) : ℤ)) ((k * karP2 c1 n P ^ s : ℕ) : ℤ),
                ‖∑ t ∈ Finset.Icc (-((k * karP2 c1 n P ^ s : ℕ) : ℤ)) ((k * karP2 c1 n P ^ s : ℕ) : ℤ),
                  eC (iteratedDeriv s f (a : ℝ) / (s.factorial : ℝ) * (t : ℝ) * (μ : ℝ))‖
            ≤ 2 ^ (8 * k) * (30 * (k : ℝ) ^ 2) * (9 * (n : ℝ)) *
              Real.log (P : ℝ) * ((karP2 c1 n P : ℝ) + 1) ^ (2 * s) *
              (P : ℝ) ^ (-(min (c1 / 3) (min c3 c4) * (s : ℝ))) := by
  intro c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 hc241
  obtain ⟨cc0, hcc0, H⟩ :=
    leaf_karW_display7_Qbounds c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 hc241
  refine ⟨cc0, hcc0, ?_⟩
  intro N P n f T a k hP hn hn0 hbig hH ha haP hnk s hs
  have hQb := H N P n f T a k hP hn hn0 hbig hH ha haP hnk s hs
  set M : ℕ := karP2 c1 n P with hM
  set b : ℝ := iteratedDeriv s f (a : ℝ) / (s.factorial : ℝ) with hb
  set K : ℕ := k * M ^ s with hK
  set ρ : ℝ := min (c1 / 3) (min c3 c4) with hρ
  set Q : ℝ := ((⌊|b|⁻¹⌋₊ : ℕ) : ℝ) with hQ
  set X : ℝ := ((M : ℝ) + 1) ^ s with hX
  have hk1 : 1 ≤ k := by nlinarith
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  -- the bounds `P^{-c2 s} ≤ |B_s| ≤ P^{-c3 s}` at the point `a`
  have haI : (a : ℝ) ∈ Set.Icc (N : ℝ) (N + P) := by
    constructor
    · exact_mod_cast ha
    · have : a ≤ N + P := by
        have := Nat.zero_le (karP2 c1 n P ^ 2); omega
      exact_mod_cast this
  have hbB := hH.2.2.2.2 s hs (a : ℝ) haI
  have hb0 : 0 < |b| := lt_of_lt_of_le (Real.rpow_pos_of_pos hP0 _) hbB.1
  have hb1 : |b| ≤ 1 := by
    refine hbB.2.trans (Real.rpow_le_one_of_one_le_of_nonpos hP1 ?_)
    have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    nlinarith
  have hQ1 : 1 ≤ Q := by
    rw [hQ]
    have : (1 : ℝ) ≤ |b|⁻¹ := by rw [one_le_inv₀ hb0]; exact hb1
    exact_mod_cast Nat.le_floor (by exact_mod_cast this)
  have hX1 : 1 ≤ X := one_le_pow₀ (by linarith [M.cast_nonneg (α := ℝ)])
  have hKX : (K : ℝ) ≤ k * X := by
    rw [hK]; push_cast
    have : (M : ℝ) ^ s ≤ X := pow_le_pow_left₀ (by positivity) (by linarith) s
    exact mul_le_mul_of_nonneg_left this (by positivity)
  -- display (6) per term
  have h6 : ∑ μ ∈ Finset.Icc (-((K : ℕ) : ℤ)) ((K : ℕ) : ℤ),
        ‖∑ t ∈ Finset.Icc (-((K : ℕ) : ℤ)) ((K : ℕ) : ℤ), eC (b * (t : ℝ) * (μ : ℝ))‖
      ≤ ∑ μ ∈ Finset.Icc (-((K : ℕ) : ℤ)) ((K : ℕ) : ℤ), karMinGeom K (b * (μ : ℝ)) := by
    refine Finset.sum_le_sum (fun μ _ => ?_)
    calc ‖∑ t ∈ Finset.Icc (-((K : ℕ) : ℤ)) ((K : ℕ) : ℤ), eC (b * (t : ℝ) * (μ : ℝ))‖
        = ‖∑ t ∈ Finset.Icc (-((K : ℕ) : ℤ)) ((K : ℕ) : ℤ), eC (b * (μ : ℝ) * (t : ℝ))‖ := by
          congr 1
          exact Finset.sum_congr rfl (fun t _ => by congr 1; ring)
      _ ≤ _ := karW_geom_min K (b * (μ : ℝ))
  have hL3 := leaf_karW_lemma3_applied b K hb0 hb1
  have har := leaf_karW_display7_arith k X (K : ℝ) Q hk1 hX1 (Nat.cast_nonneg _) hKX hQ1
  have hcast : (((2 * K + 1 : ℕ) : ℝ)) = 2 * (K : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hL3
  have hE0 : 0 ≤ 108 * (k : ℝ) ^ 2 * X ^ 2 := by positivity
  have h108 : (108 : ℝ) ≤ 2 ^ (8 * k) * 30 := by
    have : (2 : ℝ) ^ 8 ≤ 2 ^ (8 * k) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this ⊢
    linarith
  have hlogP : 0 ≤ Real.log (P : ℝ) := Real.log_nonneg hP1
  have hPr : 0 ≤ (P : ℝ) ^ (-(ρ * (s : ℝ))) := Real.rpow_nonneg hP0.le _
  have hX2 : X ^ 2 = ((M : ℝ) + 1) ^ (2 * s) := by rw [hX, ← pow_mul, mul_comm]
  refine h6.trans (hL3.trans (har.trans ?_))
  calc _ ≤ 108 * (k : ℝ) ^ 2 * X ^ 2 * (9 * (n : ℝ) * (P : ℝ) ^ (-(ρ * (s : ℝ))) * Real.log (P : ℝ)) :=
        mul_le_mul_of_nonneg_left hQb hE0
    _ ≤ 2 ^ (8 * k) * 30 * (k : ℝ) ^ 2 * X ^ 2 *
          (9 * (n : ℝ) * (P : ℝ) ^ (-(ρ * (s : ℝ))) * Real.log (P : ℝ)) := by
        gcongr
    _ = _ := by rw [hX2]; ring

example : type_of% @leaf_karW_display7_factor := leaf_karW_display7_factor_of_leaves

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
