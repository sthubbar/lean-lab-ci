/-
Feed split of `prop14_error_bound`, burst-20261122 session S107.
Zinoviev 1997, J. Number Theory 65, Proposition 1.4, proof on pp. 340 to 341, papers/P0097.
Leaves: the Abel step (1.10) with the prime powers, the progression bound for psi of p. 341
in the modulus range of Lemma 1.3 and, separately, in the range the paper does not treat,
the remainder estimate for R of p. 341, Schoenfeld's bound of reference [4] for q = 1, 2,
and the elementary count for q = 2. The glue `prop14_error_bound_of_leaves` is sorry free.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.State1546

namespace LeanLab.Zinoviev1997.State1546
open MeasureTheory

/-- `ψ(x; q, l) = Σ_{n ≤ x, n ≡ l mod q} Λ(n)`, Zinoviev 1997, p. 340, the display after (1.10). -/
noncomputable def psiMod (x : ℝ) (q l : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Iic ⌊x⌋₊).filter (fun n => n % q = l % q), ArithmeticFunction.vonMangoldt n

/-- LEAF: display (1.10), p. 340, Abel's transformation together with the prime power count.
Class MEDIUM. `Σ_{n ≤ x, n ≡ l} Λ(n)/ln n = ψ(x;q,l)/ln x + ∫₂ˣ ψ(u;q,l)/(u ln² u) du`
exactly, and it exceeds `π(x;q,l)` by the prime powers `p^k`, `k ≥ 2`, each weighted `1/k`.
The paper bounds that excess by `√x ln x / φ(q)`; here the weaker constant `0.1 √x ln x`
is used, which already follows from `#{p^k ≤ x, k ≥ 2} ≤ √x + x^{1/3} log₂ x`. -/
theorem prop14_abel {q l : ℕ} (hq : 1 ≤ q) {x : ℝ} (hx : 10 ^ 9 ≤ x) :
    |(piMod x q l : ℝ) - (psiMod x q l / Real.log x +
        ∫ u in (2 : ℝ)..x, psiMod u q l / (u * Real.log u ^ 2))| ≤
      0.1 * Real.sqrt x * Real.log x := by
  sorry

/-- LEAF: the display `ψ(x;q,l) = x/φ(q) + c √x ln² x`, `|c| ≤ 0.85`, p. 341, in the modulus
range of Lemma 1.3. Class HARD. The paper's route: orthogonality of characters, p. 340, the
reduction to primitive characters with error `Σ_{(n,q)>1} Λ(n) ln² x`, Lemma 1.3 for the
non principal characters and Schoenfeld [4] for `ψ(x)`. -/
theorem psiMod_grh_low (hG : LeanLab.DERZ1997.GRH) {q l : ℕ} (hq : 3 ≤ q)
    (hl : Nat.Coprime l q) {u : ℝ} (hu : 10 ^ 9 ≤ u) (hqu : (q : ℝ) ≤ u ^ (0.37 : ℝ)) :
    |psiMod u q l - u / (Nat.totient q : ℝ)| ≤ 0.85 * Real.sqrt u * Real.log u ^ 2 := by
  sorry

/-- LEAF: the orthogonality step, p. 340: `ψ(x;q,l) = φ(q)⁻¹ Σ_χ ψ(x,χ) χ̄(l)`, the principal
term against `ψ(x)` and each non principal `χ` against its primitive `χ₁` with error
`Σ_{(n,q)>1} Λ(n) ≤ ln² x`, then Lemma 1.3 `lemma13`, given as `h13`, on the `φ(q) - 1` others; no primitive
character mod 2 exists. Class
HARD. The `(φ(q) - 1)/φ(q)` factor is kept; the paper rounds it to `|c| ≤ 0.84`. -/
theorem psiMod_orthogonality {q l : ℕ} (hq : 3 ≤ q) (hl : Nat.Coprime l q) {u : ℝ}
    (hu : 10 ^ 9 ≤ u) (hqu : (q : ℝ) ≤ u ^ (0.37 : ℝ))
    (h13 : ∀ (k : ℕ) [NeZero k] (χ : DirichletCharacter ℂ k), χ.IsPrimitive → 3 ≤ k →
      k ∣ q → ‖psiChi χ u‖ ≤ 0.83 * Real.sqrt u * Real.log u ^ 2) :
    |psiMod u q l - psiMod u 1 0 / (Nat.totient q : ℝ)| ≤
      ((Nat.totient q : ℝ) - 1) / (Nat.totient q : ℝ) * 0.83 * Real.sqrt u * Real.log u ^ 2 +
        2 * Real.log u ^ 2 := by
  sorry

/-- LEAF: Schoenfeld 1976, reference [4], as quoted on p. 341: under RH, for `x > 75`,
`|ψ(x) - x| ≤ √x ln² x / (8π)`. Class HARD, a cited result. RH is the case `q = 1` of GRH. -/
theorem schoenfeld_psi (hG : LeanLab.DERZ1997.GRH) {x : ℝ} (hx : 75 < x) :
    |psiMod x 1 0 - x| ≤ Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) := by
  sorry

/-- The final numerics of p. 341, proved: the bounds of the orthogonality step and of
Schoenfeld combine to `|c| ≤ 0.85`. -/
theorem psiMod_low_numerics {Ψq ψ u φ : ℝ} (hφ : 1 ≤ φ) (hu : 10 ^ 9 ≤ u)
    (hA : |Ψq - ψ / φ| ≤ (φ - 1) / φ * 0.83 * Real.sqrt u * Real.log u ^ 2 +
      2 * Real.log u ^ 2)
    (hB : |ψ - u| ≤ Real.sqrt u * Real.log u ^ 2 / (8 * Real.pi)) :
    |Ψq - u / φ| ≤ 0.85 * Real.sqrt u * Real.log u ^ 2 := by
  have hφ0 : 0 < φ := by linarith
  have hL2n : 0 ≤ Real.log u ^ 2 := sq_nonneg _
  have hsq : (100 : ℝ) ≤ Real.sqrt u := by
    rw [show (100 : ℝ) = Real.sqrt (100 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by linarith)
  obtain ⟨S, hS⟩ : ∃ S, S = Real.sqrt u * Real.log u ^ 2 := ⟨_, rfl⟩
  have hSn : 0 ≤ S := by rw [hS]; positivity
  have hdec : Ψq - u / φ = (Ψq - ψ / φ) + (ψ - u) / φ := by
    rw [sub_div]; ring
  have hB1 : |ψ - u| ≤ 0.83 * S := by
    refine hB.trans ?_
    rw [div_le_iff₀ (by positivity), ← hS]
    nlinarith [Real.pi_gt_three]
  have hB' : |(ψ - u) / φ| ≤ 0.83 * S / φ := by
    rw [abs_div, abs_of_pos hφ0]
    exact div_le_div_of_nonneg_right hB1 hφ0.le
  have hfac : (φ - 1) / φ * 0.83 * Real.sqrt u * Real.log u ^ 2 = 0.83 * S - 0.83 * S / φ := by
    rw [hS, sub_div, div_self hφ0.ne']; ring
  have h2 : 2 * Real.log u ^ 2 ≤ 0.02 * S := by rw [hS]; nlinarith
  rw [hdec]
  calc |(Ψq - ψ / φ) + (ψ - u) / φ| ≤ |Ψq - ψ / φ| + |(ψ - u) / φ| := abs_add_le _ _
    _ ≤ 0.85 * S := by linarith
    _ = 0.85 * Real.sqrt u * Real.log u ^ 2 := by rw [hS]; ring

/-- `psiMod_grh_low` from `lemma13` of Decomp575a, `psiMod_orthogonality` and `schoenfeld_psi`,
with the proved numerics. The statement of `psiMod_grh_low`, copied verbatim.
CONDITIONAL ON those three, `lemma13` resting on the leaf `lemma13_explicit_budget`. -/
theorem psiMod_grh_low_of_leaves (hG : LeanLab.DERZ1997.GRH) {q l : ℕ} (hq : 3 ≤ q)
    (hl : Nat.Coprime l q) {u : ℝ} (hu : 10 ^ 9 ≤ u) (hqu : (q : ℝ) ≤ u ^ (0.37 : ℝ)) :
    |psiMod u q l - u / (Nat.totient q : ℝ)| ≤ 0.85 * Real.sqrt u * Real.log u ^ 2 := by
  have hφ : (1 : ℝ) ≤ Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hq0 : (0 : ℝ) ≤ q := by positivity
  refine psiMod_low_numerics hφ hu ?_ (schoenfeld_psi hG (by linarith))
  refine psiMod_orthogonality hq hl hu hqu ?_
  intro k _ χ hχ hk hkq
  refine lemma13 hG hk χ hχ hu ?_
  exact le_trans (by exact_mod_cast Nat.le_of_dvd (by omega) hkq) hqu

/-- LEAF: the same display of p. 341 for heights `u ≥ 10⁹` with `q > u^0.37`. Class HARD.
The proof of Proposition 1.4 integrates the bound of p. 341 over `u ∈ [10⁹, x]` while
Lemma 1.3 only covers `q ≤ u^0.37`; the paper does not treat this range. For `q > √u` the
trivial bound suffices; for `u^0.37 < q ≤ √u` a GRH bound uniform in `q` is needed. -/
theorem psiMod_grh_high (hG : LeanLab.DERZ1997.GRH) {q l : ℕ} (hq : 3 ≤ q)
    (hl : Nat.Coprime l q) {u : ℝ} (hu : 10 ^ 9 ≤ u) (hqu : u ^ (0.37 : ℝ) < (q : ℝ)) :
    |psiMod u q l - u / (Nat.totient q : ℝ)| ≤ 0.85 * Real.sqrt u * Real.log u ^ 2 := by
  sorry

/-- The final numerics of the estimate of `R`, p. 341, proved: a piece below `x₀ = 10⁹` of size
at most `10⁸ - 3` and the piece `c ∫_{x₀}^x du/√u ≤ 0.85 · 2√x` above `x₀` give the bound of
`prop14_remainder`, since `ln x ≥ 29 ln 2 > 20` for `x ≥ 10⁹`. -/
theorem prop14_remainder_numerics {I₁ I₂ x : ℝ} (hx : 10 ^ 9 ≤ x)
    (h₁ : |I₁| ≤ 10 ^ 8 - 3) (h₂ : |I₂| ≤ 0.85 * (2 * Real.sqrt x)) :
    |I₁ + I₂| ≤ 0.15 * Real.sqrt x * Real.log x + (10 ^ 8 - 3) := by
  have hL : 20 ≤ Real.log x := by
    have h29 : ((2 : ℝ) ^ 29) ≤ x := by norm_num at hx ⊢; linarith
    have := Real.log_le_log (by positivity) h29
    rw [Real.log_pow] at this
    push_cast at this
    linarith [Real.log_two_gt_d9]
  have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have : 0.85 * (2 * Real.sqrt x) ≤ 0.15 * Real.sqrt x * Real.log x := by nlinarith
  exact (abs_add_le _ _).trans (by linarith)

/-- LEAF: the estimate of `R`, p. 341, with `x₀ = 10⁹`. Class MEDIUM. Given the bound of
p. 341 on `[x₀, x]`, the trivial bound `ψ(t;q,l) ≤ ψ(t)` below `x₀` and
`∫_{x₀}^x du/√u ≤ 2√x` give `|∫₂ˣ (ψ(u;q,l) - u/φ(q))/(u ln² u) du| ≤ 0.15 √x ln x + 10⁸ - 3`.
The paper's total `0.1 √x ln x + 10⁸` also absorbs `3/φ(q)`. -/
theorem prop14_remainder {q l : ℕ} (hq : 1 ≤ q) {x : ℝ} (hx : 10 ^ 9 ≤ x)
    (hB : ∀ u ∈ Set.Icc (10 ^ 9 : ℝ) x,
      |psiMod u q l - u / (Nat.totient q : ℝ)| ≤ 0.85 * Real.sqrt u * Real.log u ^ 2) :
    |(∫ u in (2 : ℝ)..x, psiMod u q l / (u * Real.log u ^ 2)) -
        (∫ u in (2 : ℝ)..x, 1 / Real.log u ^ 2) / (Nat.totient q : ℝ)| ≤
      0.15 * Real.sqrt x * Real.log x + (10 ^ 8 - 3) := by
  sorry

/-- LEAF: Schoenfeld 1976, reference [4] of the paper, Corollary 1, as used on p. 341 for
`q = 1, 2`: under RH, `|π(x) - li(x)| < √x ln x / (8π)` for `x ≥ 2657`. Class HARD, a cited
result. Schoenfeld's `li` integrates from `0`, so `li(x) = Li(x) + li(2)` with
`li(2) < 1.05`; the `+ 2` covers that shift. RH is the case `q = 1` of GRH. -/
theorem schoenfeld_pi (hG : LeanLab.DERZ1997.GRH) {x : ℝ} (hx : 2657 ≤ x) :
    |(piMod x 1 0 : ℝ) - zinLi x| ≤ Real.sqrt x * Real.log x / (8 * Real.pi) + 2 := by
  sorry

/-- `π(x; 2, l) = π(x) - 1` for odd `l` and `x ≥ 2`, p. 341 "If q = 1, 2 then
π(x; q, l) is π(x)". Proved. -/
theorem piMod_two {l : ℕ} (hl : Nat.Coprime l 2) {x : ℝ} (hx : 2 ≤ x) :
    (piMod x 2 l : ℝ) = piMod x 1 0 - 1 := by
  have hl2 : l % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one l with h | h
    · exfalso
      have : 2 ∣ Nat.gcd l 2 := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h) dvd_rfl
      rw [hl] at this; omega
    · exact h
  have h2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hset : (Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ p % 1 = 0 % 1) =
      insert 2 ((Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ p % 2 = l % 2)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_insert, Nat.mod_one, hl2]
    constructor
    · rintro ⟨hp, hpr, -⟩
      rcases hpr.eq_two_or_odd with h | h
      · left; exact h
      · right; exact ⟨hp, hpr, h⟩
    · rintro (rfl | ⟨hp, hpr, -⟩)
      · exact ⟨h2, Nat.prime_two, trivial⟩
      · exact ⟨hp, hpr, trivial⟩
  have hnot : 2 ∉ (Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ p % 2 = l % 2) := by
    simp [hl2]
  unfold piMod
  rw [hset, Finset.card_insert_of_notMem hnot]
  push_cast; ring


/-- `π(x; 1, l) = π(x)`, p. 341. -/
theorem piMod_one (x : ℝ) (l : ℕ) : piMod x 1 l = piMod x 1 0 := by
  simp [piMod, Nat.mod_one]

/-- Proposition 1.4 error form, Zinoviev 1997 pp. 339 to 341, from the leaves above.
The statement of `prop14_error_bound`, copied verbatim.
CONDITIONAL ON `prop14_abel`, `psiMod_grh_low`, `psiMod_grh_high`, `prop14_remainder`,
and `schoenfeld_pi`. -/
theorem prop14_error_bound_of_leaves (hG : LeanLab.DERZ1997.GRH) {q l : ℕ}
    (hq : 1 ≤ q) (hl : Nat.Coprime l q) {x : ℝ} (hx : 10 ^ 9 ≤ x)
    (hqx : (q : ℝ) ≤ x ^ (0.37 : ℝ)) :
    |(piMod x q l : ℝ) - zinLi x / (Nat.totient q : ℝ)| ≤
      1.3 * Real.sqrt x * Real.log x + 10 ^ 8 := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hS : 0 ≤ Real.sqrt x * Real.log x := mul_nonneg (Real.sqrt_nonneg x) hL.le
  rcases Nat.lt_or_ge q 3 with h3 | h3
  · -- q = 1 or q = 2, Schoenfeld
    have hsch := schoenfeld_pi hG (x := x) (by linarith)
    have hpi : Real.sqrt x * Real.log x / (8 * Real.pi) ≤ Real.sqrt x * Real.log x := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_gt_three]
    interval_cases q
    · rw [piMod_one]
      simp only [Nat.totient_one, Nat.cast_one, div_one]
      linarith
    · rw [piMod_two hl (by linarith)]
      simp only [Nat.totient_two, Nat.cast_one, div_one]
      rw [show (piMod x 1 0 : ℝ) - 1 - zinLi x = ((piMod x 1 0 : ℝ) - zinLi x) - 1 by ring]
      refine (abs_sub _ _).trans ?_
      rw [abs_one]
      linarith
  · have hφ : (1 : ℝ) ≤ Nat.totient q := by
      exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hφ0 : (0 : ℝ) < Nat.totient q := by linarith
    have hB : ∀ u ∈ Set.Icc (10 ^ 9 : ℝ) x,
        |psiMod u q l - u / (Nat.totient q : ℝ)| ≤ 0.85 * Real.sqrt u * Real.log u ^ 2 := by
      intro u hu
      rcases le_or_gt (q : ℝ) (u ^ (0.37 : ℝ)) with h | h
      · exact psiMod_grh_low hG h3 hl hu.1 h
      · exact psiMod_grh_high hG h3 hl hu.1 h
    have hA := prop14_abel (l := l) hq hx
    have hR := prop14_remainder (l := l) hq hx hB
    have hX := hB x ⟨hx, le_rfl⟩
    have hLi := zinLi_by_parts (x := x) (by linarith)
    have hlog2 : 0.69 < Real.log 2 := by linarith [Real.log_two_gt_d9]
    set P : ℝ := (piMod x q l : ℝ)
    set Ψ : ℝ := psiMod x q l
    set I : ℝ := ∫ u in (2 : ℝ)..x, psiMod u q l / (u * Real.log u ^ 2)
    set J : ℝ := ∫ u in (2 : ℝ)..x, 1 / Real.log u ^ 2
    set φ : ℝ := (Nat.totient q : ℝ)
    set L : ℝ := Real.log x
    have hdec : P - zinLi x / φ =
        (P - (Ψ / L + I)) + (Ψ - x / φ) / L + (I - J / φ) + 2 / (Real.log 2 * φ) := by
      rw [hLi]
      field_simp
      ring
    have hmid : |(Ψ - x / φ) / L| ≤ 0.85 * Real.sqrt x * L := by
      rw [abs_div, abs_of_pos hL, div_le_iff₀ hL]
      nlinarith
    have hlast : |2 / (Real.log 2 * φ)| ≤ 3 := by
      rw [abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
      nlinarith
    rw [hdec]
    have h4 := (abs_add_le (P - (Ψ / L + I) + (Ψ - x / φ) / L + (I - J / φ))
      (2 / (Real.log 2 * φ))).trans (add_le_add
        (abs_add_three (P - (Ψ / L + I)) ((Ψ - x / φ) / L) (I - J / φ)) le_rfl)
    have hR' : |I - J / φ| ≤ 0.15 * Real.sqrt x * L + (10 ^ 8 - 3) := hR
    have hA' : |P - (Ψ / L + I)| ≤ 0.1 * Real.sqrt x * L := hA
    nlinarith

end LeanLab.Zinoviev1997.State1546
