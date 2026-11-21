/-
CITED WALL SESSION 2026-11-20, step leaf_near_zero_selected of
`LeanLab.ExceptionalSet.UpJ200.Decomp559b`.
P0082, Bruedern and Perelli 1998, Ann. Inst. Fourier 48, pages 353 to 378,
https://doi.org/10.5802/aif.1621. Lemma 7 case ii d, page 364, with
display 10 on page 358 and Lemma 3 with displays 11 to 15 on pages 358 and 359.

DECISION, verdict NAMED HYPOTHESIS. The leaf is the paper's case ii d with
the divisor sums Gamma_1 and Gamma_2 kept explicit. Its two cited inputs are
1. display 10, the classical lower bound for the distance of a real zero of
   a real primitive L function from one, Davenport chapter 14, and
2. the case ii d major arc lower bound on page 364, the display after
   "From (20) we now infer", which rests on Lemma 3, that is (6.17) of
   Montgomery and Vaughan with the error of (6.19) kept explicit, together
   with the singular series inequality (21).
Both become named hypotheses below, and the exact leaf statement is
assembled from them with no sorry: the step from
r^{-1/2} (log r)^{-2} and r at most E^{1/7} to E^{-1/10} is proved here.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.UpJ200.Decomp559b

namespace LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelected

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.Decomp559b (SelectedRealZero)

/-- NAMED HYPOTHESIS, cited theorem. P0082 page 358 display 10, left
inequality, citing Davenport, Multiplicative Number Theory, chapter 14:
a real zero beta of the L function of a real nonprincipal primitive
character of modulus r satisfies r^{-1/2} (log r)^{-2} << 1 - beta.
Written multiplied out, c0 at most (1 - beta) r^{1/2} (log r)^2, which is
the same statement for every modulus r at least 3, the only moduli that
carry such a character. -/
def RealZeroDistanceHyp : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
    χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
      ∀ β : ℝ, 0 < β → β < 1 → χ.LFunction β = 0 →
        c₀ ≤ (1 - β) * (r : ℝ) ^ (1 / 2 : ℝ) * Real.log r ^ 2

/-- NAMED HYPOTHESIS, cited lemma. P0082 page 364, case ii d of Lemma 7,
the display after "From (20) we now infer", with P = X^{6 delta} and
X = F(N) as on page 357. For an even m with X/2 < m at most X, sharing a
factor with the selected conductor r and with the product in display 21
empty, one has R_1(m) >> (1 - beta)(log P) X once delta is small. The
paper's factor m / phi(m), at least one, is dropped, and the terms
X Gamma_1(m) and X Gamma_2(m) of Lemma 3, page 358, are kept explicit
through the envelopes of displays 14 and 15, which `divisorError` encodes.
Source chain: Lemma 3 is (6.17) of Montgomery and Vaughan with (6.19) kept
explicit, and the main term bound uses display 21 and I(m) at most
m^beta. -/
def CaseIIdMajorLowerHyp : Prop :=
  ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ a : ℝ, 0 < a →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
          SelectedRealZero a (F γ N ^ (6 * δ)) r →
          ∀ m : ℤ, Even m → F γ N / 2 < (m : ℝ) → (m : ℝ) ≤ F γ N →
            1 < Int.gcd m r →
            (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ m) →
            ∀ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
              χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 0 < β →
              1 - a / Real.log (F γ N ^ (6 * δ)) ≤ β → β < 1 →
              χ.LFunction β = 0 →
                C * (1 - β) * Real.log (F γ N ^ (6 * δ)) * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) m).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) m

/-- Elementary: L^2 is at most exp(L/35) once L is at least 105^3.
Used for E^{-1/14} (log E)^{-2} >> E^{-1/10} on page 364. -/
theorem sq_le_exp_div (L : ℝ) (hL : (105 : ℝ) ^ 3 ≤ L) :
    L ^ 2 ≤ Real.exp (L / 35) := by
  have hL0 : 0 ≤ L := le_trans (by positivity) hL
  have h1 : L / 105 ≤ Real.exp (L / 105) := by
    have := Real.add_one_le_exp (L / 105); linarith
  have h2 : (L / 105) ^ 3 ≤ Real.exp (L / 105) ^ 3 :=
    pow_le_pow_left₀ (by positivity) h1 3
  have h3 : Real.exp (L / 105) ^ 3 = Real.exp (L / 35) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h4 : L ^ 2 ≤ (L / 105) ^ 3 := by
    have : L ^ 2 * (105 : ℝ) ^ 3 ≤ L ^ 2 * L :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    have e : (L / 105) ^ 3 = L ^ 2 * L / (105 : ℝ) ^ 3 := by ring
    rw [e, le_div_iff₀ (by positivity)]; exact this
  linarith

/-- P0082 page 364, the last two lines of case ii d: with display 10 and
r at most E^{1/7}, c0 E^{-1/10} is at most 1 - beta once log E is large. -/
theorem distance_lower (c₀ β E : ℝ) (r : ℕ) (hr : 1 ≤ r) (hE : 0 < E)
    (hL : (105 : ℝ) ^ 3 ≤ Real.log E) (hβ : β < 1)
    (hrE : (r : ℝ) ≤ E ^ (1 / 7 : ℝ))
    (hc : c₀ ≤ (1 - β) * (r : ℝ) ^ (1 / 2 : ℝ) * Real.log r ^ 2) :
    c₀ * E ^ (-(1 / 10 : ℝ)) ≤ 1 - β := by
  set L := Real.log E with hLdef
  have hL0 : 0 ≤ L := le_trans (by positivity) hL
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hβ' : 0 < 1 - β := by linarith
  have hsqrt : (r : ℝ) ^ (1 / 2 : ℝ) ≤ E ^ (1 / 14 : ℝ) := by
    have := Real.rpow_le_rpow hr0.le hrE (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← Real.rpow_mul hE.le] at this
    norm_num at this ⊢; exact this
  have hlogr0 : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hlogr : Real.log r ≤ L := by
    have h := Real.log_le_log hr0 hrE
    rw [Real.log_rpow hE] at h
    nlinarith
  have hlogsq : Real.log r ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hlogr0 hlogr 2
  have hexp14 : E ^ (1 / 14 : ℝ) = Real.exp (L / 14) := by
    rw [Real.rpow_def_of_pos hE]; congr 1; ring
  have hexp10 : E ^ (1 / 10 : ℝ) = Real.exp (L / 14) * Real.exp (L / 35) := by
    rw [Real.rpow_def_of_pos hE, ← Real.exp_add]; congr 1; ring
  have hkey : (r : ℝ) ^ (1 / 2 : ℝ) * Real.log r ^ 2 ≤ E ^ (1 / 10 : ℝ) := by
    rw [hexp10]
    calc (r : ℝ) ^ (1 / 2 : ℝ) * Real.log r ^ 2 ≤ E ^ (1 / 14 : ℝ) * L ^ 2 :=
          mul_le_mul hsqrt hlogsq (by positivity) (by positivity)
      _ ≤ Real.exp (L / 14) * Real.exp (L / 35) := by
          rw [hexp14]
          exact mul_le_mul_of_nonneg_left (sq_le_exp_div L hL) (by positivity)
  have hc' : c₀ ≤ (1 - β) * E ^ (1 / 10 : ℝ) := by
    calc c₀ ≤ (1 - β) * ((r : ℝ) ^ (1 / 2 : ℝ) * Real.log r ^ 2) := by
          rw [← mul_assoc]; exact hc
      _ ≤ (1 - β) * E ^ (1 / 10 : ℝ) := mul_le_mul_of_nonneg_left hkey hβ'.le
  have hpos : 0 < E ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hE _
  rw [Real.rpow_neg hE.le, ← div_eq_mul_inv, div_le_iff₀ hpos]
  exact hc'

/-- Eventual size of the two logarithms, from 1 < gamma < 3/2. -/
theorem eventually_logs (γ δ κ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      1 ≤ 6 * δ * Real.log N ^ γ ∧ (105 : ℝ) ^ 3 ≤ κ * Real.log N ^ (3 - 2 * γ) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hA : Tendsto (fun N : ℕ => 6 * δ * Real.log N ^ γ) atTop atTop :=
    ((tendsto_rpow_atTop (by linarith)).comp hlog).const_mul_atTop (by positivity)
  have hB : Tendsto (fun N : ℕ => κ * Real.log N ^ (3 - 2 * γ)) atTop atTop :=
    ((tendsto_rpow_atTop (by linarith)).comp hlog).const_mul_atTop hκ
  exact eventually_atTop.mp ((hA.eventually_ge_atTop 1).and (hB.eventually_ge_atTop _))

/-- P0082 page 364 case ii d and page 358 display 10. The exact statement of
`Decomp559b.leaf_near_zero_selected`, from the two named hypotheses.
CONDITIONAL ON `CaseIIdMajorLowerHyp` and `RealZeroDistanceHyp`; no sorry. -/
theorem leaf_near_zero_selected_of_hyps
    (hII : CaseIIdMajorLowerHyp) (hZ : RealZeroDistanceHyp)
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) → ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n + j) r →
                (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + j) →
                (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
                c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  obtain ⟨c₀, hc₀, hZ⟩ := hZ
  obtain ⟨δ₀, hδ₀, hII⟩ := hII γ h1 h2 a ha
  refine ⟨δ₀, hδ₀, fun δ hδ hδlt => ?_⟩
  obtain ⟨C, A, hC, hA, N₁, hII⟩ := hII δ hδ hδlt
  refine ⟨1, one_pos, fun κ hκ _ => ?_⟩
  obtain ⟨N₂, hN₂⟩ := eventually_logs γ δ κ h1 h2 hδ hκ
  refine ⟨C * c₀, A, mul_pos hC hc₀, hA, max N₁ N₂, ?_⟩
  intro N hN r hr1 hrP hsel j hj n hn hev hle hgcd hprod hrE
  obtain ⟨hlogP1, hlogE⟩ := hN₂ N (le_of_max_le_right hN)
  have hF : 0 < F γ N := Real.exp_pos _
  have hlogF : Real.log (F γ N) = Real.log N ^ γ := Real.log_exp _
  have hlogP : Real.log (F γ N ^ (6 * δ)) = 6 * δ * Real.log N ^ γ := by
    rw [Real.log_rpow hF, hlogF]
  have hEpos : 0 < calE γ κ N := Real.exp_pos _
  have hlogcalE : Real.log (calE γ κ N) = κ * Real.log N ^ (3 - 2 * γ) := Real.log_exp _
  have hsel' := hsel
  rcases hsel with ⟨rfl, _⟩ | ⟨hrz, χ, β, hp, hreal, hne, hβ0, hβlo, hβ1, hz, _⟩
  · simp at hgcd
  have hmem := (Finset.mem_filter.mp hn).2.1
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := by
    rcases hj with rfl | rfl <;> norm_num
  have hlow : F γ N / 2 < (((nu γ n + j : ℤ)) : ℝ) := by
    push_cast; linarith
  have hmain := hII N (le_of_max_le_left hN) r hr1 hrP hsel' (nu γ n + j) hev hlow hle
    hgcd hprod hrz χ β hp hreal hne hβ0 hβlo hβ1 hz
  have hdist := distance_lower c₀ β (calE γ κ N) r hr1 hEpos (by rw [hlogcalE]; exact hlogE)
    hβ1 hrE (hZ r hrz χ hp hreal hne β hβ0 hβ1 hz)
  have hβ' : 0 ≤ 1 - β := by linarith
  calc C * c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))
        = C * F γ N * (c₀ * calE γ κ N ^ (-(1 / 10 : ℝ))) := by ring
    _ ≤ C * F γ N * (1 - β) := mul_le_mul_of_nonneg_left hdist (by positivity)
    _ ≤ C * F γ N * (1 - β) * Real.log (F γ N ^ (6 * δ)) := by
        rw [hlogP]
        exact le_mul_of_one_le_right (by positivity) hlogP1
    _ = C * (1 - β) * Real.log (F γ N ^ (6 * δ)) * F γ N := by ring
    _ ≤ _ := hmain

/-- Twin check: the assembled theorem has exactly the type of the sealed
leaf `Decomp559b.leaf_near_zero_selected`. -/
theorem leaf_near_zero_selected_twin
    (hII : CaseIIdMajorLowerHyp) (hZ : RealZeroDistanceHyp) :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_near_zero_selected :=
  leaf_near_zero_selected_of_hyps hII hZ

end LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelected

#print axioms LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelected.sq_le_exp_div
#print axioms LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelected.distance_lower
#print axioms LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelected.eventually_logs
#print axioms LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelected.leaf_near_zero_selected_of_hyps
#print axioms LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelected.leaf_near_zero_selected_twin
