import LeanLab.LPZ2007.D4Final

/-!
P0045 preprint page 6, the remark after display 10.
The proof of displays 11 to 25 needs only uniformly diverging odd radicals.
This generalizes the existing major arc deduction and keeps its repaired constant.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007.GrowingModuli373

open Finset Real Filter MeasureTheory Eq14FromCor42 Eq3Reduce

/-- P0045 page 6, remark after display 10, and displays 11 to 25.
CONDITIONAL ON the displayed binary major arc estimates with a uniformly
bounded exceptional family whose odd radicals have any lower bound tending to infinity.
Lemma 6.2 and the singular series asymptotics are already proved in the lab. -/
theorem eq25_of_diverging_radicals
    (hC : ∃ η0 : ℝ, 0 < η0 ∧ ∀ η : ℝ, 0 < η → η < η0 →
      ∃ (Cstar C1 : ℕ) (B : ℝ) (g : ℝ → ℝ), 1 ≤ Cstar ∧
        Tendsto g atTop atTop ∧ ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
          ∃ P : ℝ, PRange X P ∧ ∃ rs : Finset ℕ, rs.card ≤ C1 ∧
            (∀ r ∈ rs, g X ≤ oddRad r) ∧
            (∀ n : ℕ, Even n → X / 2 ≤ n → (n : ℝ) ≤ X →
              (∀ r ∈ rs, ¬ r ∣ Cstar * n) →
                ‖RM X P n - n * sing n‖ ≤ η * n * sing n) ∧
            (∀ n : ℕ, Even n → X / 2 ≤ n → (n : ℝ) ≤ X →
              ‖RM X P n‖ ≤ B * n * sing n)) :
    Eq25C (fun k N => twoC0 * Ckn k N) := by
  have h62 : Lemma62 := Lemma62Port.lemma62_A
  have h3 : R3Asymp := D4Final.r3Asymp_proved
  classical
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨η0, hη0, HC⟩ := hC
  set Cm := ∑' d, romanovTerm d with hCm
  have hc0 : 0 ≤ twoC0 := twoC0_pos.le
  refine ⟨twoC0 * Cm + 3, min η0 1, lt_min hη0 one_pos, fun η hη hηlt => ?_⟩
  have hη1 : η ≤ 1 := (lt_of_lt_of_le hηlt (min_le_right _ _)).le
  obtain ⟨Cstar, C1, Bc, g, hCs, hg, Xorig, HX⟩ := HC η hη (lt_of_lt_of_le hηlt (min_le_left _ _))
  set ε := η / ((|Bc| + 1) * (C1 + 1)) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨r0, X62, H62⟩ := h62 ε hε0
  obtain ⟨X3, H3⟩ := h3 (j + 1) hk η hη
  obtain ⟨Xg, hXg⟩ := Filter.eventually_atTop.1
    (hg.eventually_ge_atTop (((r0 : ℝ) + 1) * Cstar))
  let X0c := max Xorig Xg
  set Lmin : ℝ := 36 * ((j + 1 : ℕ) : ℝ) ^ 2 + 1 with hLmin
  refine ⟨max (max X0c X62) (max X3 (max 64 ((2 : ℝ) ^ Lmin))), fun X hX => ?_⟩
  have hXc : X0c ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX62 : X62 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX3 : X3 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX64 : 64 ≤ X := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hX
  have hXL : (2 : ℝ) ^ Lmin ≤ X := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hX
  have hX0 : 0 < X := by linarith
  have hL : Lmin ≤ Lg X := Lg_ge hXL
  rw [hLmin] at hL
  have hL36 : 36 * ((j + 1 : ℕ) : ℝ) ^ 2 ≤ Lg X := by
    have := hL; push_cast at this ⊢; linarith
  have hL1 : 1 ≤ Lg X := by linarith [sq_nonneg (((j + 1 : ℕ) : ℝ))]
  have hL0 : 0 ≤ Lg X := by linarith
  obtain ⟨P, hPR, rs, hcard, hrs, hgood, hall⟩ := HX X ((le_max_left Xorig Xg).trans hXc)
  obtain ⟨hP0, hPX⟩ := prange_ok hX64 hPR
  refine ⟨P, hPR, fun N hNe hNJ => ?_⟩
  set M := ⌊Lp X⌋₊ with hM
  have hNX : (N : ℝ) ≤ X := hNJ.2
  have hN23 : 2 * X / 3 ≤ N := hNJ.1
  -- the window facts
  have hsmall : ∀ ν ∈ tuples (j + 1) M, (pow2sum ν : ℝ) ≤ X / 6 :=
    fun ν hν => pow2sum_small (by omega) hX0 hL36 hν
  have hlt : ∀ ν ∈ tuples (j + 1) M, pow2sum ν < N := by
    intro ν hν
    have := hsmall ν hν
    exact_mod_cast (show (pow2sum ν : ℝ) < N by linarith)
  have hwinν : ∀ ν ∈ tuples (j + 1) M, X / 2 ≤ ((N - pow2sum ν : ℕ) : ℝ) ∧
      ((N - pow2sum ν : ℕ) : ℝ) ≤ X ∧ ((N - pow2sum ν : ℕ) : ℝ) ≤ N ∧ Even (N - pow2sum ν) := by
    intro ν hν
    have h1 := hsmall ν hν
    have h2 := hlt ν hν
    rw [Nat.cast_sub h2.le]
    refine ⟨by linarith, by linarith [(Nat.cast_nonneg (pow2sum ν) : (0 : ℝ) ≤ _)],
      by linarith [(Nat.cast_nonneg (pow2sum ν) : (0 : ℝ) ≤ _)], ?_⟩
    exact (Nat.even_sub h2.le).2 ⟨fun _ => even_pow2sum hν, fun _ => hNe⟩
  have hwint : ∀ t ∈ tuples j M, X / 2 ≤ ((N - pow2sum t : ℕ) : ℝ) := by
    intro t ht
    have hk' : (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by push_cast; linarith
    have h1 : (pow2sum t : ℝ) ≤ X / 6 := by
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj; simp [pow2sum]; linarith
      · exact pow2sum_small hj hX0 (le_trans (by nlinarith) hL36) ht
    have h2 : pow2sum t ≤ N := by exact_mod_cast (show (pow2sum t : ℝ) ≤ N by linarith)
    rw [Nat.cast_sub h2]; linarith
  -- Step 1
  rw [RMpp_expand (j + 1) hP0 hPX N (fun ν hν => (hlt ν hν).le)]
  -- Step 2, (11) and (12)
  have hsplit := split_bound (j + 1) X P N Cstar rs (η := η) (abs_nonneg Bc) hη.le
    (fun ν hν hG => by
      obtain ⟨w1, w2, _, w4⟩ := hwinν ν hν
      have := hgood _ w4 w1 w2 hG
      push_cast at this ⊢; exact this)
    (fun ν hν => by
      obtain ⟨w1, w2, _, w4⟩ := hwinν ν hν
      refine (hall _ w4 w1 w2).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
        (Nat.cast_nonneg _)) (sing_nonneg _))
  -- (14): the moduli `s(r)`
  let s : ℕ → ℕ := fun r => oddRad r / Nat.gcd (oddRad r) Cstar
  have hJ2 := J2_bound j X N Cstar rs s ε
    (fun r _ n hn => (sMod_spec r Cstar hCs).2.1 n hn)
    (fun r hr m hm1 hm2 => by
      obtain ⟨hodd, _, hsC⟩ := sMod_spec r Cstar hCs
      refine H62 X hX62 m hm1 hm2 (s r) hodd ?_
      have hCs' : (0 : ℝ) < Cstar := by exact_mod_cast hCs
      have hgX : ((r0 : ℝ) + 1) * Cstar ≤ g X :=
        hXg X ((le_max_right Xorig Xg).trans hXc)
      have h1 : (r0 : ℝ) * Cstar ≤ oddRad r :=
        (by nlinarith : (r0 : ℝ) * Cstar ≤ ((r0 : ℝ) + 1) * Cstar).trans
          (hgX.trans (hrs r hr))
      have h2 : (r0 : ℝ) * Cstar ≤ (s r : ℝ) * Cstar := h1.trans hsC
      exact_mod_cast le_of_mul_le_mul_right h2 hCs')
    hNX hlt hwint
  -- the `J₂` sum with the weight `n_ν ≤ N`
  set Q : ℝ := (N : ℝ) * Lg X ^ (j + 1) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hbadw : ∑ ν ∈ (tuples (j + 1) M).filter (fun ν => ¬ Good rs Cstar (N - pow2sum ν)),
      ((N - pow2sum ν : ℕ) : ℝ) * sing (N - pow2sum ν) ≤
      N * (rs.card * (M : ℝ) ^ j * (ε * Lg X)) := by
    refine le_trans (sum_le_sum fun ν hν => mul_le_mul_of_nonneg_right
      (hwinν ν (mem_filter.1 hν).1).2.2.1 (sing_nonneg _)) ?_
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left hJ2 (Nat.cast_nonneg _)
  have hMj : (M : ℝ) ^ j ≤ Lg X ^ j := by
    have hsq : √(Lg X) ≤ Lg X := by
      calc √(Lg X) ≤ √(Lg X ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = Lg X := Real.sqrt_sq hL0
    have hMp : (M : ℝ) ≤ Lp X := Nat.floor_le (by unfold Lp; linarith)
    have : Lp X ≤ Lg X := by unfold Lp; linarith [Real.sqrt_nonneg (Lg X)]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hMp.trans this) j
  have hepsC : (|Bc| + 1) * rs.card * ε ≤ η := by
    have hC1 : (rs.card : ℝ) ≤ C1 := by exact_mod_cast hcard
    have hpos : 0 < (|Bc| + 1) * ((C1 : ℝ) + 1) := by positivity
    calc (|Bc| + 1) * rs.card * ε ≤ (|Bc| + 1) * C1 * ε := by gcongr
      _ = η * (C1 / (C1 + 1)) := by rw [hε]; field_simp
      _ ≤ η * 1 := by
          gcongr; rw [div_le_one (by positivity)]; linarith
      _ = η := mul_one η
  have hbad : (|Bc| + 1) * ∑ ν ∈ (tuples (j + 1) M).filter
      (fun ν => ¬ Good rs Cstar (N - pow2sum ν)),
        ((N - pow2sum ν : ℕ) : ℝ) * sing (N - pow2sum ν) ≤ η * Q := by
    refine le_trans (mul_le_mul_of_nonneg_left hbadw (by positivity)) ?_
    have hrw : (|Bc| + 1) * (N * (rs.card * (M : ℝ) ^ j * (ε * Lg X))) =
        ((|Bc| + 1) * rs.card * ε) * (N * (M : ℝ) ^ j * Lg X) := by ring
    rw [hrw, hQ, pow_succ]
    have h1 : (N : ℝ) * (M : ℝ) ^ j * Lg X ≤ N * Lg X ^ j * Lg X := by gcongr
    have h2 : 0 ≤ (N : ℝ) * (M : ℝ) ^ j * Lg X := by positivity
    calc ((|Bc| + 1) * rs.card * ε) * (N * (M : ℝ) ^ j * Lg X) ≤ η * (N * (M : ℝ) ^ j * Lg X) :=
          mul_le_mul_of_nonneg_right hepsC h2
      _ ≤ η * (N * Lg X ^ j * Lg X) := mul_le_mul_of_nonneg_left h1 hη.le
      _ = η * (N * (Lg X ^ j * Lg X)) := by ring
  -- (15) to (24)
  have hR3 := H3 X hX3 N hNe hNJ
  set T : ℝ := twoC0 * Ckn (j + 1) N * N * Lg X ^ (j + 1) with hT
  have hTle : T ≤ twoC0 * Cm * Q := by
    rw [hT, hQ, mul_assoc (twoC0 * Ckn (j + 1) N)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Corollary.Ckn_bounds j N).2 hc0) hQ0
  have hR3' : |R3 (j + 1) X N - T| ≤ η * Q := by rw [hQ, ← mul_assoc]; exact hR3
  have hR3up : R3 (j + 1) X N ≤ twoC0 * Cm * Q + η * Q := by
    have := (abs_le.1 hR3').2; linarith
  have hηR3 : η * R3 (j + 1) X N ≤ η * (twoC0 * Cm * Q) + η * Q := by
    have h1 := mul_le_mul_of_nonneg_left hR3up hη.le
    have h2 : η * (η * Q) ≤ η * Q := by
      have := mul_le_mul_of_nonneg_right hη1 (mul_nonneg hη.le hQ0); linarith
    linarith
  -- assemble
  have hcast : (((twoC0 * Ckn (j + 1) N : ℝ) : ℂ) * (N : ℂ) * ((Lg X : ℝ) : ℂ) ^ (j + 1)) =
      ((T : ℝ) : ℂ) := by rw [hT]; push_cast; ring
  simp only at hcast ⊢
  rw [hcast]
  have htri : ‖(∑ ν ∈ tuples (j + 1) M, RM X P (N - pow2sum ν)) - ((T : ℝ) : ℂ)‖ ≤
      ‖(∑ ν ∈ tuples (j + 1) M, RM X P (N - pow2sum ν)) - ((R3 (j + 1) X N : ℝ) : ℂ)‖ +
        |R3 (j + 1) X N - T| := by
    refine (norm_sub_le_norm_sub_add_norm_sub _ (((R3 (j + 1) X N : ℝ) : ℂ)) _).trans ?_
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hgoal : (twoC0 * Cm + 3) * η * N * Lg X ^ (j + 1) = (twoC0 * Cm + 3) * η * Q := by
    rw [hQ]; ring
  rw [hgoal]
  have hfin : (twoC0 * Cm + 3) * η * Q = η * (twoC0 * Cm * Q) + 3 * (η * Q) := by ring
  rw [hfin]
  linarith [hsplit, htri, hbad, hηR3, hR3']

/-- P0045 page 6, display 10 implies the qualitative growth condition in the remark.
This bridge keeps the same P, exceptional family and binary estimates as Cor42W.
It is CONDITIONAL ON Cor42W. -/
theorem diverging_radicals_of_cor42W (h : Cor42W) :
    ∃ η0 : ℝ, 0 < η0 ∧ ∀ η : ℝ, 0 < η → η < η0 →
      ∃ (Cstar C1 : ℕ) (B : ℝ) (g : ℝ → ℝ), 1 ≤ Cstar ∧
        Tendsto g atTop atTop ∧ ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
          ∃ P : ℝ, PRange X P ∧ ∃ rs : Finset ℕ, rs.card ≤ C1 ∧
            (∀ r ∈ rs, g X ≤ oddRad r) ∧
            (∀ n : ℕ, Even n → X / 2 ≤ n → (n : ℝ) ≤ X →
              (∀ r ∈ rs, ¬ r ∣ Cstar * n) →
                ‖RM X P n - n * sing n‖ ≤ η * n * sing n) ∧
            (∀ n : ℕ, Even n → X / 2 ≤ n → (n : ℝ) ≤ X →
              ‖RM X P n‖ ≤ B * n * sing n) := by
  obtain ⟨η0, hη0, H⟩ := h
  refine ⟨η0, hη0, ?_⟩
  intro η hη hηsmall
  obtain ⟨Cstar, C1, c, B, X0, hCs, hc, HX⟩ := H η hη hηsmall
  refine ⟨Cstar, C1, B, (fun X => c * Lg X ^ 2), hCs, ?_, X0, HX⟩
  exact ((Filter.tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2))).const_mul_atTop hc

end LeanLab.LPZ2007.GrowingModuli373

#print axioms LeanLab.LPZ2007.GrowingModuli373.eq25_of_diverging_radicals

#print axioms LeanLab.LPZ2007.GrowingModuli373.diverging_radicals_of_cor42W
