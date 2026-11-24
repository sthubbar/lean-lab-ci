/-
P0083 Perelli 1996, pages 484 and 485, displays 19 through 24.
ROUTE BURST S79 burst-20261122 split of Char1122.leaf_bad_character_removal, display 24.
Display 20 and display 23 are new LEAFs; the step from them to 24, through the full
period Parseval bound of CharacterMoment632 and the totient factor of CharacterTail632,
is proved here.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Char1122
import LeanLab.Perelli1996.CharacterMoment632
import LeanLab.Perelli1996.CharacterTail632

namespace LeanLab.Perelli1996.Bad1122
open Finset Real Polynomial MeasureTheory
open LeanLab.Perelli1996.Decomp88 LeanLab.Perelli1996.Decomp582a LeanLab.Perelli1996.Char1122
open scoped ArithmeticFunction.vonMangoldt
noncomputable section

attribute [local instance] Classical.propDecidable

/-- LEAF: Page 484 display 20, from the zero free region 19 of Prachar Chapter 8 together
with Siegel's theorem: for every ε' > 0, a bad character modulo q forces q ≫_{ε'} L^(1/(2ε')).
Here P stands for 1/(2ε'), so P > 0 is arbitrary, and L = log N.
Class HARD. Cited inputs: Prachar Chapter 8 and Siegel's theorem. -/
theorem leaf_bad_modulus_large (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) (P : ℝ) (hP : 0 < P) :
    ∃ c' N₀ : ℝ, 0 < c' ∧ 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), ¬ goodCharacter B ε N χ →
        c' * Real.log N ^ P ≤ q := by
  sorry

/-- LEAF: Page 485 display 23, from the character expansion of R(η,q,a) before display 16,
Cauchy-Schwarz with the Gauss sum bound τ(χ) ≪ q^(1/2), and the count 22 of bad characters
obtained from the density estimate 21. The paper prints the bad character factor as
q/φ(q)² L^(50B/ε) max_{χ bad} ∫|W(χ,η)|²; here the fixed power of L is L^e with e
depending only on F, the density constants, c, ε and B, and the maximum is any bound X
for the bad character integrals. The final term L⁴/(qQ) of 23 is already absorbed into
N L^(-B), as the paper does when passing to 24.
Class MEDIUM. CONDITIONAL ON display 21 through hDensity. -/
theorem leaf_character_expansion (F : ℤ[X]) (hF : Admissible F)
    (C d : ℝ) (hC : 0 < C) (hd : 0 < d) (hDensity : DensityInput C d)
    (c : ℝ) (hc : 0 < c) (ε B : ℝ) (hε : 0 < ε) (hB : 0 < B) :
    ∃ e C' N₀ : ℝ, 0 ≤ e ∧ 0 < C' ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ fareyOrder F N H B →
      ∀ a : ℤ, Nat.Coprime a.natAbs q →
      ∀ X : ℝ, 0 ≤ X →
      (∀ χ : DirichletCharacter ℂ q, ¬ goodCharacter B ε N χ →
        (∫ η in (-(1 / ((q : ℝ) * fareyOrder F N H B)))..
          (1 / ((q : ℝ) * fareyOrder F N H B)), ‖twistedRemainder ⌊c * N⌋₊ χ η‖ ^ 2) ≤ X) →
      (∫ η in (-(1 / ((q : ℝ) * fareyOrder F N H B)))..
        (1 / ((q : ℝ) * fareyOrder F N H B)),
        ‖characterRemainder ⌊c * N⌋₊ q a η‖ ^ 2) ≤
        C' * ((q : ℝ) / (q.totient : ℝ) ^ 2 * Real.log N ^ e * X +
          goodEnergy B ε N ⌊c * N⌋₊ q (fareyOrder F N H B) + N * Real.log N ^ (-B)) := by
  sorry

/-- The good character energy is nonnegative. -/
theorem goodEnergy_nonneg (B ε N : ℝ) (M q : ℕ) [NeZero q] (Q : ℝ) (hQ : 0 < Q) :
    0 ≤ goodEnergy B ε N M q Q := by
  unfold goodEnergy
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro χ _
  split_ifs
  · apply intervalIntegral.integral_nonneg
    · have : 0 < 1 / ((q : ℝ) * Q) := by positivity
      linarith
    · intro η _; positivity
  · exact le_refl 0

/-- A bad character integral over |η| ≤ 1/(qQ) is at most the full period integral. -/
theorem arc_le_full_period (M q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (r : ℝ)
    (hr : 0 < r) (hr2 : r ≤ 1 / 2) :
    (∫ η in (-r)..r, ‖twistedRemainder M χ η‖ ^ 2) ≤
      ∫ η in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), ‖twistedRemainder M χ η‖ ^ 2 := by
  have hcont : Continuous (fun η => ‖twistedRemainder M χ η‖ ^ 2) :=
    ((continuous_twistedRemainder M χ).norm).pow 2
  apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) hr2
  · exact Filter.Eventually.of_forall (fun η => by positivity)
  · exact hcont.intervalIntegrable _ _

/-- Page 485 display 24, the exact statement of Char1122.leaf_bad_character_removal,
proved from the two LEAFs above, the full period bound character_full_period_scaled and
bad_character_totient_factor. The choice P = e + B + 4 plays the role of ε' = ε/(200B).
CONDITIONAL ON display 21 and the LEAFs leaf_bad_modulus_large and
leaf_character_expansion. -/
theorem bad_character_removal_of_split (F : ℤ[X]) (hF : Admissible F)
    (C d : ℝ) (hC : 0 < C) (hd : 0 < d) (hDensity : DensityInput C d)
    (c : ℝ) (hc : 0 < c) (ε B : ℝ) (hε : 0 < ε) (hB : 0 < B) :
    ∃ C' N₀ : ℝ, 0 < C' ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ fareyOrder F N H B →
      ∀ a : ℤ, Nat.Coprime a.natAbs q →
      (∫ η in (-(1 / ((q : ℝ) * fareyOrder F N H B)))..
        (1 / ((q : ℝ) * fareyOrder F N H B)),
        ‖characterRemainder ⌊c * N⌋₊ q a η‖ ^ 2) ≤
        C' * (goodEnergy B ε N ⌊c * N⌋₊ q (fareyOrder F N H B) +
          N * Real.log N ^ (-B)) := by
  obtain ⟨e, C1, N1, he, hC1, hN1, h23⟩ :=
    leaf_character_expansion F hF C d hC hd hDensity c hc ε B hε hB
  obtain ⟨CP, NP, hCP, hNP, hfull⟩ := character_full_period_scaled c hc
  obtain ⟨c', N2, hc', hN2, h20⟩ := leaf_bad_modulus_large B ε hB hε (e + B + 4) (by positivity)
  obtain ⟨NA, hNA, harc⟩ := arc_parameters F hF ε B hε hB
  let K := 16 * CP / c' + 1
  refine ⟨C1 * K, max (max N1 NP) (max N2 (max NA (Real.exp 1))), by positivity,
    hN1.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro N H hN hH hHu q _ hqQ a hcop
  have hN1' : N1 ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNP' : NP ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hN2' : N2 ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNA' : NA ≤ N :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hN
  have hNE : Real.exp 1 ≤ N :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hN
  have hN0 : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hNE
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) hNE
  have hL0 : 0 < Real.log N := by linarith
  set Q := fareyOrder F N H B with hQdef
  have hQ2 : 2 ≤ Q := (harc N H hNA' hH).2
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
  have hr : 0 < 1 / ((q : ℝ) * Q) := by positivity
  have hr2 : 1 / ((q : ℝ) * Q) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num); nlinarith
  set gE := goodEnergy B ε N ⌊c * N⌋₊ q Q with hgE
  have hg0 : 0 ≤ gE := goodEnergy_nonneg B ε N _ q Q (by linarith)
  have hP0 : 0 ≤ N * Real.log N ^ (-B) := by positivity
  have hK1 : 1 ≤ K := by dsimp [K]; have : 0 ≤ 16 * CP / c' := by positivity
                         linarith
  by_cases hbad : ∃ χ : DirichletCharacter ℂ q, ¬ goodCharacter B ε N χ
  · obtain ⟨χ₀, hχ₀⟩ := hbad
    have hqbig : c' * Real.log N ^ (e + B + 4) ≤ q := h20 N hN2' q χ₀ hχ₀
    let Xb := CP * N * Real.log N
    have hX : 0 ≤ Xb := by positivity
    have hbound : ∀ χ : DirichletCharacter ℂ q, ¬ goodCharacter B ε N χ →
        (∫ η in (-(1 / ((q : ℝ) * Q)))..(1 / ((q : ℝ) * Q)),
          ‖twistedRemainder ⌊c * N⌋₊ χ η‖ ^ 2) ≤ Xb := by
      intro χ _
      refine (arc_le_full_period _ q χ _ hr hr2).trans ?_
      have hf := hfull N hNP' q χ (if χ = 1 then 1 else 0) (by split_ifs <;> simp)
      have heq : (fun η => ‖twistedRemainder ⌊c * N⌋₊ χ η‖ ^ 2) =
          (fun η => ‖(∑ n ∈ range (⌊c * N⌋₊ + 1), (Λ n : ℂ) * χ n * Kernel.e ((n : ℝ) * η)) -
            (if χ = 1 then (1 : ℂ) else 0) * Kernel.T 0 (⌊c * N⌋₊ + 1) η‖ ^ 2) := by
        funext η; unfold twistedRemainder; split_ifs <;> simp
      rw [heq]; exact hf
    have hmain := h23 N H hN1' hH hHu q hqQ a hcop Xb hX hbound
    -- the bad character term
    have hlogq : Real.log q ≤ Real.log N := by
      have hHk : H ^ F.natDegree ≤ N := by
        have h0 : 0 ≤ H := le_trans (by positivity) hH
        calc H ^ F.natDegree ≤ (N ^ (1 / (F.natDegree : ℝ))) ^ F.natDegree := by gcongr
          _ = N := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
            have : (F.natDegree : ℝ) ≠ 0 := by
              exact_mod_cast (show F.natDegree ≠ 0 by have := hF.1; omega)
            rw [one_div_mul_cancel this, Real.rpow_one]
      have hQN : Q ≤ N := by
        rw [hQdef]; unfold fareyOrder
        have hy : H ^ F.natDegree * Real.log N ^ (-B / 4) ≤ N := by
          have : Real.log N ^ (-B / 4) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
          have h0 : 0 ≤ H ^ F.natDegree := pow_nonneg (le_trans (by positivity) hH) _
          nlinarith
        have hs : Real.sqrt (H ^ F.natDegree * Real.log N ^ (-B / 4)) ≤ N := by
          rw [Real.sqrt_le_left]
          · nlinarith [hL1, Real.add_one_le_exp 1, hNE]
          · exact hN0.le
        linarith
      exact Real.log_le_log (by linarith) (by linarith)
    have hfac := bad_character_totient_factor q hqpos (Real.log N) hL1 hlogq
    have hpowq : 0 < c' * Real.log N ^ (e + B + 4) := by positivity
    have hbadterm : (q : ℝ) / (q.totient : ℝ) ^ 2 * Real.log N ^ e * Xb ≤
        16 * CP / c' * (N * Real.log N ^ (-B)) := by
      have hLe : 0 ≤ Real.log N ^ e := by positivity
      calc (q : ℝ) / (q.totient : ℝ) ^ 2 * Real.log N ^ e * Xb
          ≤ 16 * Real.log N ^ 2 / q * Real.log N ^ e * Xb := by gcongr
        _ = 16 * CP * N * (Real.log N ^ (e + 3)) / q := by
            dsimp [Xb]
            rw [Real.rpow_add hL0, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            ring
        _ ≤ 16 * CP * N * (Real.log N ^ (e + 3)) / (c' * Real.log N ^ (e + B + 4)) := by
            gcongr
        _ = 16 * CP / c' * (N * Real.log N ^ (-B - 1)) := by
            have h1 : Real.log N ^ (e + B + 4) = Real.log N ^ (e + 3) * Real.log N ^ (B + 1) := by
              rw [← Real.rpow_add hL0]; ring_nf
            have h2 : Real.log N ^ (-B - 1) = (Real.log N ^ (B + 1))⁻¹ := by
              rw [← Real.rpow_neg hL0.le]; ring_nf
            rw [h1, h2]
            have : 0 < Real.log N ^ (e + 3) := by positivity
            have : 0 < Real.log N ^ (B + 1) := by positivity
            field_simp
        _ ≤ 16 * CP / c' * (N * Real.log N ^ (-B)) := by
            gcongr
            linarith
    calc _ ≤ C1 * ((q : ℝ) / (q.totient : ℝ) ^ 2 * Real.log N ^ e * Xb + gE +
          N * Real.log N ^ (-B)) := hmain
      _ ≤ C1 * (16 * CP / c' * (N * Real.log N ^ (-B)) + gE + N * Real.log N ^ (-B)) := by
          gcongr
      _ ≤ C1 * K * (gE + N * Real.log N ^ (-B)) := by
          dsimp [K]
          have h16 : 0 ≤ 16 * CP / c' := by positivity
          have := mul_nonneg h16 hg0
          nlinarith
  · push_neg at hbad
    have hbound : ∀ χ : DirichletCharacter ℂ q, ¬ goodCharacter B ε N χ →
        (∫ η in (-(1 / ((q : ℝ) * Q)))..(1 / ((q : ℝ) * Q)),
          ‖twistedRemainder ⌊c * N⌋₊ χ η‖ ^ 2) ≤ 0 := by
      intro χ hχ; exact absurd (hbad χ) hχ
    have hmain := h23 N H hN1' hH hHu q hqQ a hcop 0 le_rfl hbound
    calc _ ≤ C1 * ((q : ℝ) / (q.totient : ℝ) ^ 2 * Real.log N ^ e * 0 + gE +
          N * Real.log N ^ (-B)) := hmain
      _ = C1 * 1 * (gE + N * Real.log N ^ (-B)) := by ring
      _ ≤ C1 * K * (gE + N * Real.log N ^ (-B)) := by gcongr

/-- Pages 484 and 485 displays 16 through 25, the same statement as
Char1122.leaf_character_of_split, with display 24 from bad_character_removal_of_split. The exact statement of
Decomp88.leaf_character, restricted to B ≥ B₀, CONDITIONAL ON Decomp582a.leaf_zero_density, Char1122.leaf_good_character_mean and the
two LEAFs of this file, for B at least the B₀ of leaf_good_character_mean.
The assembly itself has no sorry. -/
theorem leaf_character_of_split2 (F : ℤ[X]) (hF : Admissible F)
    (c : ℝ) (hc : 0 < c) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ ε B : ℝ, 0 < ε → B₀ ≤ B →
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ fareyOrder F N H B →
      ∀ a : ℤ, Nat.Coprime a.natAbs q →
      (∫ η in (-(1 / ((q : ℝ) * fareyOrder F N H B)))..
        (1 / ((q : ℝ) * fareyOrder F N H B)),
        ‖characterRemainder ⌊c * N⌋₊ q a η‖ ^ 2) ≤ C * N * Real.log N ^ (-B) := by
  obtain ⟨CD, d, hCD, hd, hDensity⟩ := leaf_zero_density
  obtain ⟨B₀, hB₀, h25all⟩ := leaf_good_character_mean F hF CD d hCD hd hDensity c hc
  refine ⟨B₀, hB₀, ?_⟩
  intro ε B hε hBB
  have hB : 0 < B := hB₀.trans_le hBB
  obtain ⟨C1, N1, hC1, hN1, h24⟩ :=
    bad_character_removal_of_split F hF CD d hCD hd hDensity c hc ε B hε hB
  obtain ⟨C2, N2, hC2, hN2, h25⟩ := h25all ε B hε hBB
  refine ⟨C1 * (C2 + 1), max N1 N2, by positivity, hN1.trans (le_max_left _ _), ?_⟩
  intro N H hN hH hHu q hq hqQ a hcop
  haveI : NeZero q := ⟨hq.ne'⟩
  have hb := h24 N H ((le_max_left _ _).trans hN) hH hHu q hqQ a hcop
  have hg := h25 N H ((le_max_right _ _).trans hN) hH hHu q hqQ
  have hN0 : 0 < N := by linarith [hN1.trans ((le_max_left N1 N2).trans hN)]
  have hP : 0 ≤ N * Real.log N ^ (-B) := by
    have : 0 < Real.log N := Real.log_pos (by linarith [hN1.trans ((le_max_left N1 N2).trans hN)])
    positivity
  calc _ ≤ C1 * (goodEnergy B ε N ⌊c * N⌋₊ q (fareyOrder F N H B) +
          N * Real.log N ^ (-B)) := hb
    _ ≤ C1 * (C2 * N * Real.log N ^ (-B) + N * Real.log N ^ (-B)) := by gcongr
    _ = C1 * (C2 + 1) * N * Real.log N ^ (-B) := by ring

end
end LeanLab.Perelli1996.Bad1122
