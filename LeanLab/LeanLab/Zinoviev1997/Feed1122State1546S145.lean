/-
Split of `psiMod_grh_high`, unit s145 grhhigh. Zinoviev 1997, J. Number Theory 65, p. 341,
the range `q > u^0.37` that the paper does not treat. The range `q > √u` is elementary
and proved here; the range `u^0.37 < q ≤ √u` rests on a cited GRH bound
uniform in the modulus and on the orthogonality step of p. 340 for `q ≤ √u`.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.Feed1122State1546

namespace LeanLab.Zinoviev1997.State1546
open MeasureTheory

/-- The trivial bound for `ψ(u;q,l)`, proved: at most `u/q + 1` integers `n ≤ u` lie in one
residue class mod `q`, and `Λ(n) ≤ ln u`. -/
theorem s145g_psiMod_trivial {q l : ℕ} (hq : 1 ≤ q) {u : ℝ} (hu : 1 ≤ u) :
    psiMod u q l ≤ (u / q + 1) * Real.log u := by
  set N := ⌊u⌋₊
  set S := (Finset.Iic N).filter (fun n => n % q = l % q)
  have hcard : S.card ≤ N / q + 1 := by
    have : S.card ≤ (Finset.range (N / q + 1)).card := by
      refine Finset.card_le_card_of_injOn (fun n => n / q) ?_ ?_
      · intro n hn
        simp only [S, Finset.coe_filter, Finset.mem_Iic, Set.mem_ofPred_eq] at hn
        simp only [Finset.coe_range, Set.mem_Iio]
        exact Nat.lt_succ_of_le (Nat.div_le_div_right hn.1)
      · intro n hn m hm hnm
        simp only [S, Finset.coe_filter, Finset.mem_Iic, Set.mem_ofPred_eq] at hn hm
        simp only at hnm
        rw [← Nat.div_add_mod n q, ← Nat.div_add_mod m q, hnm, hn.2, hm.2]
    simpa using this
  have hlog : ∀ n ∈ S, ArithmeticFunction.vonMangoldt n ≤ Real.log u := by
    intro n hn
    simp only [S, Finset.mem_filter, Finset.mem_Iic] at hn
    refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp [Real.log_nonneg hu]
    · exact Real.log_le_log (by exact_mod_cast hpos)
        ((Nat.cast_le.mpr hn.1).trans (Nat.floor_le (by linarith)))
  have hsum : psiMod u q l ≤ S.card • Real.log u := Finset.sum_le_card_nsmul _ _ _ hlog
  rw [nsmul_eq_mul] at hsum
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hNq : ((N / q : ℕ) : ℝ) ≤ u / q := by
    refine (Nat.cast_div_le).trans ?_
    exact div_le_div_of_nonneg_right (Nat.floor_le (by linarith)) hq0.le
  have hc : (S.card : ℝ) ≤ u / q + 1 := by
    have : (S.card : ℝ) ≤ ((N / q : ℕ) : ℝ) + 1 := by exact_mod_cast hcard
    linarith
  exact hsum.trans (mul_le_mul_of_nonneg_right hc (Real.log_nonneg hu))

/-- For distinct integers `p ≥ 2`, `Π p ≤ (#s + 1) Π (p - 1)`, by induction on the maximum. -/
theorem s145g_prod_le (s : Finset ℕ) (hs : ∀ p ∈ s, 2 ≤ p) :
    ∏ p ∈ s, p ≤ (s.card + 1) * ∏ p ∈ s, (p - 1) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have ha2 : 2 ≤ a := hs a (Finset.mem_insert_self a s)
    have ih' := ih (fun p hp => hs p (Finset.mem_insert_of_mem hp))
    have hsub : s ⊆ Finset.Ico 2 a := by
      intro p hp
      rw [Finset.mem_Ico]
      exact ⟨hs p (Finset.mem_insert_of_mem hp), ha p hp⟩
    have hc : s.card + 2 ≤ a := by
      have := Finset.card_le_card hsub
      rw [Nat.card_Ico] at this
      omega
    rw [Finset.prod_insert has, Finset.prod_insert has, Finset.card_insert_of_notMem has]
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    set P := ∏ p ∈ s, p
    set Q := ∏ p ∈ s, (p - 1)
    set c := s.card
    calc (b + 1) * P ≤ (b + 1) * ((c + 1) * Q) := Nat.mul_le_mul_left _ ih'
      _ = ((b + 1) * (c + 1)) * Q := by ring
      _ ≤ ((c + 1 + 1) * b) * Q := by
          apply Nat.mul_le_mul_right; nlinarith
      _ = (c + 1 + 1) * (b * Q) := by ring

/-- An elementary lower bound for Euler's function, proved, needed for the main term `u/φ(q)`
in the range `q > √u`, not in the paper: `q/φ(q) = Π_{p ∣ q} p/(p-1) ≤ ω(q) + 1 ≤ 1 + log₂ q`. -/
theorem s145g_totient_lower {q : ℕ} (hq : 1 ≤ q) :
    (q : ℝ) ≤ (Nat.totient q : ℝ) * (1 + Real.logb 2 q) := by
  have hT := Nat.totient_mul_prod_primeFactors q
  have hP := s145g_prod_le q.primeFactors (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have hQ : 0 < ∏ p ∈ q.primeFactors, (p - 1) := Finset.prod_pos fun p hp => by
    have := (Nat.prime_of_mem_primeFactors hp).two_le; omega
  set c := q.primeFactors.card
  have h1 : q ≤ Nat.totient q * (c + 1) := by
    have : q * ∏ p ∈ q.primeFactors, (p - 1) ≤
        (Nat.totient q * (c + 1)) * ∏ p ∈ q.primeFactors, (p - 1) := by
      rw [← hT]; calc Nat.totient q * ∏ p ∈ q.primeFactors, p
          ≤ Nat.totient q * ((c + 1) * ∏ p ∈ q.primeFactors, (p - 1)) :=
            Nat.mul_le_mul_left _ hP
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right this hQ
  have h2 : 2 ^ c ≤ q := by
    calc 2 ^ c ≤ ∏ p ∈ q.primeFactors, p := Finset.pow_card_le_prod _ _ _
          (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ q := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
  have h3 : (c : ℝ) ≤ Real.logb 2 q := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hq)]
    rw [Real.rpow_natCast]; exact_mod_cast h2
  have h1' : (q : ℝ) ≤ (Nat.totient q : ℝ) * ((c : ℝ) + 1) := by exact_mod_cast h1
  have hφ : (0 : ℝ) ≤ Nat.totient q := Nat.cast_nonneg _
  nlinarith

/-- LEAF: the bound of Lemma 1.3 of the paper, p. 339, for a primitive character, extended to
the conductor range `k ≤ √u`; class HARD, a cited result. Under GRH, for `χ` primitive mod
`k ≥ 3`, `u ≥ 10⁹` and `k ≤ √u`, `|ψ(u, χ)| ≤ 0.83 √u ln² u`. Citation: an explicit GRH bound
for `ψ(x, χ)` uniform in the modulus, Lamzouri, Li, Soundararajan, Math. Comp. 84, 2015,
or Ernvall-Hytönen and Palojärvi, arXiv 2003.01925; those bounds have the shape
`√x ln x · (c₁ ln x + c₂ ln k)/(2π)` plus lower order terms, and with `ln k ≤ ln u / 2` this
is below `0.83 √u ln² u`; the exact constants of the citation are still to be checked. -/
theorem s145g_psiChi_grh_uniform (hG : LeanLab.DERZ1997.GRH) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (χ : DirichletCharacter ℂ k) (hχ : χ.IsPrimitive) {u : ℝ} (hu : 10 ^ 9 ≤ u)
    (hku : (k : ℝ) ≤ Real.sqrt u) :
    ‖psiChi χ u‖ ≤ 0.83 * Real.sqrt u * Real.log u ^ 2 := by
  sorry

/-- The imprimitive error of p. 340 in the wide range `q ≤ √u`: `ω(q) ln u ≤ 2 ln² u`.
Proved, as `s145_E_bound` with `ln q ≤ ln u / 2`. -/
theorem s145g_E_bound_wide {q : ℕ} (hq : 3 ≤ q) {u : ℝ} (hu : 10 ^ 9 ≤ u)
    (hqu : (q : ℝ) ≤ Real.sqrt u) :
    ∑ n ∈ (Finset.Iic ⌊u⌋₊).filter (fun n => ¬ n.Coprime q), ArithmeticFunction.vonMangoldt n ≤
      2 * Real.log u ^ 2 := by
  have hu0 : 0 < u := by linarith
  have hN : 1 ≤ ⌊u⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hlogN : Real.log (⌊u⌋₊ : ℕ) ≤ Real.log u :=
    Real.log_le_log (by exact_mod_cast hN) (Nat.floor_le hu0.le)
  have hL0 : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have hω := s145_omega_le (q := q) (by omega)
  have hlq : Real.log q ≤ Real.log u / 2 := by
    have := Real.log_le_log (by exact_mod_cast (by omega : 0 < q)) hqu
    rwa [Real.log_sqrt hu0.le] at this
  have hl2 := Real.log_two_gt_d9
  have hE := s145_E_le (q := q) (N := ⌊u⌋₊) (by omega) hN
  set ω : ℝ := (q.primeFactors.card : ℝ)
  have hω0 : 0 ≤ ω := by positivity
  have hω2 : ω ≤ 2 * Real.log u := by nlinarith
  calc _ ≤ ω * Real.log (⌊u⌋₊ : ℕ) := hE
    _ ≤ ω * Real.log u := mul_le_mul_of_nonneg_left hlogN hω0
    _ ≤ (2 * Real.log u) * Real.log u := mul_le_mul_of_nonneg_right hω2 hL0
    _ = 2 * Real.log u ^ 2 := by ring

/-- Proved in this file by S145, formerly a LEAF of class MEDIUM: the orthogonality step of p. 340, as in `psiMod_orthogonality`, for the wider
modulus range `q ≤ √u`; class MEDIUM. `ψ(x;q,l) = φ(q)⁻¹ Σ_χ ψ(x,χ) χ̄(l)`, each character
replaced by its primitive one with error `Σ_{p ∣ q, p^m ≤ u} ln p ≤ ω(q) ln u ≤ 0.73 ln² u`
since `q ≤ √u`, which `2 ln² u` covers. -/
theorem s145g_psiMod_orthogonality_wide {q l : ℕ} (hq : 3 ≤ q) (hl : Nat.Coprime l q) {u : ℝ}
    (hu : 10 ^ 9 ≤ u) (hqu : (q : ℝ) ≤ Real.sqrt u)
    (h13 : ∀ (k : ℕ) [NeZero k] (χ : DirichletCharacter ℂ k), χ.IsPrimitive → 3 ≤ k →
      k ∣ q → ‖psiChi χ u‖ ≤ 0.83 * Real.sqrt u * Real.log u ^ 2) :
    |psiMod u q l - psiMod u 1 0 / (Nat.totient q : ℝ)| ≤
      ((Nat.totient q : ℝ) - 1) / (Nat.totient q : ℝ) * 0.83 * Real.sqrt u * Real.log u ^ 2 +
        2 * Real.log u ^ 2 := by
  haveI : NeZero q := ⟨by omega⟩
  set E := ∑ n ∈ (Finset.Iic ⌊u⌋₊).filter (fun n => ¬ n.Coprime q),
    ArithmeticFunction.vonMangoldt n with hEdef
  have hE2 : E ≤ 2 * Real.log u ^ 2 := s145g_E_bound_wide hq hu hqu
  set S := 0.83 * Real.sqrt u * Real.log u ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
  set φ : ℝ := (Nat.totient q : ℝ) with hφ
  have hφ1 : 1 ≤ φ := by
    have : 0 < q.totient := Nat.totient_pos.mpr (by omega)
    rw [hφ]; exact_mod_cast this
  have ha : IsUnit (l : ZMod q) := (ZMod.isUnit_iff_coprime l q).mpr hl
  have hai : IsUnit ((l : ZMod q)⁻¹) := ⟨⟨_, _, ZMod.inv_mul_of_unit _ ha, ZMod.mul_inv_of_unit _ ha⟩, rfl⟩
  -- the orthogonality identity, split at the principal character
  have hid := s145_orth (u := u) hl
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ q)),
    MulChar.one_apply hai, one_mul] at hid
  -- principal term
  have hP : ‖psiChi (1 : DirichletCharacter ℂ q) u - (psiMod u 1 0 : ℂ)‖ ≤ E := by
    rw [norm_sub_rev, s145_psiMod_one]
    refine s145_diff (fun _ => (1 : ℂ)) (fun n => (1 : DirichletCharacter ℂ q) (n : ZMod q))
      ?_ ?_ ?_
    · intro n hn
      exact (MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hn)).symm
    · intro n hn
      exact MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
    · intro n; simp
  -- non principal terms
  have hcard : (((Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1).card : ℝ) = φ - 1 := by
    have h1 := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    rw [Nat.card_eq_fintype_card] at h1
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, h1, hφ]
    have : 1 ≤ q.totient := Nat.totient_pos.mpr (by omega)
    push_cast [this]; ring
  have hN : ‖∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
      χ ((l : ZMod q)⁻¹) * psiChi χ u‖ ≤ (φ - 1) * (S + E) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, (S + E) := by
          apply Finset.sum_le_sum
          intro χ hχ
          rw [norm_mul]
          have h1 := DirichletCharacter.norm_le_one χ ((l : ZMod q)⁻¹)
          have h2 := s145_nonprincipal h13 χ (Finset.ne_of_mem_erase hχ)
          have h3 : 0 ≤ ‖psiChi χ u‖ := norm_nonneg _
          calc ‖χ ((l : ZMod q)⁻¹)‖ * ‖psiChi χ u‖ ≤ 1 * ‖psiChi χ u‖ :=
                mul_le_mul_of_nonneg_right h1 h3
            _ ≤ S + E := by rw [one_mul]; exact h2
      _ = (φ - 1) * (S + E) := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
  -- combine
  have hD : ‖(φ : ℂ) * (psiMod u q l : ℂ) - (psiMod u 1 0 : ℂ)‖ ≤ (φ - 1) * S + φ * E := by
    rw [hφ, Complex.ofReal_natCast, ← hid]
    have he : psiChi (1 : DirichletCharacter ℂ q) u + ∑ χ ∈ (Finset.univ : Finset
        (DirichletCharacter ℂ q)).erase 1, χ ((l : ZMod q)⁻¹) * psiChi χ u - (psiMod u 1 0 : ℂ) =
        (psiChi (1 : DirichletCharacter ℂ q) u - (psiMod u 1 0 : ℂ)) + ∑ χ ∈ (Finset.univ : Finset
        (DirichletCharacter ℂ q)).erase 1, χ ((l : ZMod q)⁻¹) * psiChi χ u := by ring
    rw [he]
    refine (norm_add_le _ _).trans ?_
    nlinarith
  have hφ0 : 0 < φ := by linarith
  have hreal : psiMod u q l - psiMod u 1 0 / φ = (φ * psiMod u q l - psiMod u 1 0) / φ := by
    field_simp
  rw [hreal, abs_div, abs_of_pos hφ0, div_le_iff₀ hφ0]
  have hc : |φ * psiMod u q l - psiMod u 1 0| =
      ‖(φ : ℂ) * (psiMod u q l : ℂ) - (psiMod u 1 0 : ℂ)‖ := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hc]
  refine hD.trans ?_
  have : (φ - 1) / φ * 0.83 * Real.sqrt u * Real.log u ^ 2 * φ = (φ - 1) * S := by
    rw [hS]; field_simp
  nlinarith

theorem s145g_log_ge_20 {u : ℝ} (hu : 10 ^ 9 ≤ u) : 20 ≤ Real.log u := by
  have h29 : ((2 : ℝ) ^ 29) ≤ u := by norm_num at hu ⊢; linarith
  have := Real.log_le_log (by positivity) h29
  rw [Real.log_pow] at this
  push_cast at this
  linarith [Real.log_two_gt_d9]

theorem s145g_psiMod_nonneg (u : ℝ) (q l : ℕ) : 0 ≤ psiMod u q l :=
  Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

/-- The range `q > √u`, proved sorry free from the trivial count and the totient bound. -/
theorem s145g_high_range {q l : ℕ} (hq : 3 ≤ q) {u : ℝ} (hu : 10 ^ 9 ≤ u)
    (hqs : Real.sqrt u < (q : ℝ)) :
    |psiMod u q l - u / (Nat.totient q : ℝ)| ≤ 0.85 * Real.sqrt u * Real.log u ^ 2 := by
  have hL := s145g_log_ge_20 hu
  have hu0 : 0 < u := by linarith
  have hs0 : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
  have hss : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0.le
  have hsq : (100 : ℝ) ≤ Real.sqrt u := by
    rw [show (100 : ℝ) = Real.sqrt (100 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by linarith)
  have hq0 : (0 : ℝ) < q := by linarith
  have hφ0 : (0 : ℝ) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  -- the prime side
  have ha0 := s145g_psiMod_nonneg u q l
  have ha := s145g_psiMod_trivial (q := q) (l := l) (by omega) (by linarith : (1 : ℝ) ≤ u)
  have huq : u / q ≤ Real.sqrt u := by
    rw [div_le_iff₀ hq0]; nlinarith
  have ha' : psiMod u q l ≤ (Real.sqrt u + 1) * Real.log u := by
    refine ha.trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  -- the main term
  have hT := s145g_totient_lower (q := q) (by omega)
  have hl2 : 0.69 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  have hlq : Real.log q ≤ Real.log u + q / u := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (q : ℝ) / u by positivity)
    rw [Real.log_div hq0.ne' hu0.ne'] at h
    linarith
  have huq0 : 0 ≤ u / q := by positivity
  have hkey : u / q * Real.log q ≤ Real.sqrt u * Real.log u + 1 := by
    have h1 : u / q * Real.log q ≤ u / q * (Real.log u + q / u) :=
      mul_le_mul_of_nonneg_left hlq huq0
    have h2 : u / q * (q / u) = 1 := by field_simp
    have h3 : u / q * Real.log u ≤ Real.sqrt u * Real.log u :=
      mul_le_mul_of_nonneg_right huq (by linarith)
    nlinarith
  set X : ℝ := 1 + Real.logb 2 q with hX
  have hX0 : 0 < X := by
    have : 0 ≤ Real.logb 2 (q : ℝ) := Real.logb_nonneg (by norm_num) (by linarith)
    linarith
  have hb0 : 0 ≤ u / (Nat.totient q : ℝ) := by positivity
  have hb1 : u / (Nat.totient q : ℝ) ≤ u / q * X := by
    rw [div_le_iff₀ hφ0]
    have : u / q * q ≤ u / q * ((Nat.totient q : ℝ) * X) := mul_le_mul_of_nonneg_left hT huq0
    rw [div_mul_cancel₀ _ hq0.ne'] at this
    linarith
  have hb2 : u / q * X = u / q + u / q * Real.log q / Real.log 2 := by
    rw [hX, Real.logb]; ring
  have hb3 : u / q * Real.log q / Real.log 2 ≤ (Real.sqrt u * Real.log u + 1) / 0.69 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    have : 0 ≤ u / q * Real.log q := mul_nonneg huq0 hlq0
    nlinarith
  have hb : u / (Nat.totient q : ℝ) ≤
      Real.sqrt u + (Real.sqrt u * Real.log u + 1) / 0.69 := by
    linarith
  have hB : Real.sqrt u + (Real.sqrt u * Real.log u + 1) / 0.69 ≤
      0.85 * Real.sqrt u * Real.log u ^ 2 := by
    have hSL0 : 0 ≤ Real.sqrt u * Real.log u := by positivity
    have e1 : 20 * (Real.sqrt u * Real.log u) ≤ Real.sqrt u * Real.log u * Real.log u :=
      by nlinarith
    have e2 : Real.sqrt u * 20 ≤ Real.sqrt u * Real.log u :=
      mul_le_mul_of_nonneg_left hL hs0.le
    have e3 : 0.85 * Real.sqrt u * Real.log u ^ 2 =
      0.85 * (Real.sqrt u * Real.log u * Real.log u) := by ring
    rw [e3, div_eq_mul_inv]
    norm_num
    nlinarith
  have hA : (Real.sqrt u + 1) * Real.log u ≤ 0.85 * Real.sqrt u * Real.log u ^ 2 := by
    nlinarith
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The range `u^0.37 < q ≤ √u`, from the cited uniform GRH LEAF, the wide orthogonality
LEAF, `schoenfeld_psi` and the proved numerics `psiMod_low_numerics`. -/
theorem s145g_mid_range (hG : LeanLab.DERZ1997.GRH) {q l : ℕ} (hq : 3 ≤ q)
    (hl : Nat.Coprime l q) {u : ℝ} (hu : 10 ^ 9 ≤ u) (hqs : (q : ℝ) ≤ Real.sqrt u) :
    |psiMod u q l - u / (Nat.totient q : ℝ)| ≤ 0.85 * Real.sqrt u * Real.log u ^ 2 := by
  have hφ : (1 : ℝ) ≤ Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  refine psiMod_low_numerics hφ hu ?_ (schoenfeld_psi hG (by linarith))
  refine s145g_psiMod_orthogonality_wide hq hl hu hqs ?_
  intro k _ χ hχ hk hkq
  refine s145g_psiChi_grh_uniform hG hk χ hχ hu ?_
  exact le_trans (by exact_mod_cast Nat.le_of_dvd (by omega) hkq) hqs

/-- `psiMod_grh_high` from the LEAFs above, statement copied verbatim. -/
theorem psiMod_grh_high_of_s145_leaves (hG : LeanLab.DERZ1997.GRH) {q l : ℕ} (hq : 3 ≤ q)
    (hl : Nat.Coprime l q) {u : ℝ} (hu : 10 ^ 9 ≤ u) (hqu : u ^ (0.37 : ℝ) < (q : ℝ)) :
    |psiMod u q l - u / (Nat.totient q : ℝ)| ≤ 0.85 * Real.sqrt u * Real.log u ^ 2 := by
  clear hqu
  rcases le_or_gt (q : ℝ) (Real.sqrt u) with h | h
  · exact s145g_mid_range hG hq hl hu h
  · exact s145g_high_range hq hu h

end LeanLab.Zinoviev1997.State1546

