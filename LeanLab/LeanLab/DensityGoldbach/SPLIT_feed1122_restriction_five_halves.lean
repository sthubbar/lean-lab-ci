/-
Split of `Decomp408b.restriction_five_halves`, burst-20261122 feed1122, session S89.

Source: Shao, arXiv 1206.6139v2, page 17, Lemma 4.6 at q = 5/2, which cites
B. Green, Roth's theorem in the primes, arXiv math/0302311, Lemma 6.6, whose proof rests on
the Bourgain style large spectrum estimate `#{r : |f^(r)| ≥ δ} ≪_ε δ^{-2-ε}` for
`0 ≤ f ≤ ν_b`, followed by a dyadic summation over the levels `δ`.

Structure:
* LEAF `large_spectrum_mid_nine_quarters`: the large spectrum estimate at the exponent
  `q = 9/4`, only for levels `δ < δ₀` that lie above the Parseval line
  `K δ^{-9/4} < 2 log(z# N) δ^{-2}`. This is exactly the window where Bourgain's argument with
  Green's enveloping sieve is needed. The lab's proved bound `U1502.greenLargeSpec` is at
  exponent `q = 3`, and its eighth moment core gives `8/3`; both exceed `5/2`, so a higher
  moment of the Ramanujan majorant is required here.
* PROVED `small_nine_quarters`: the very small levels by Parseval, copied from
  `U1494.small_of_mid` with the exponent kept explicit.
* PROVED `largeSpec_nine_quarters`: the large levels `δ ≥ δ₀` by TT* and `U1484.green62`,
  copied from `U1494.largeSpec_of_small` with the exponent kept explicit.
* PROVED `restriction_five_halves_split`: `U1488.dyadic_sum` with `q = 9/4 < p = 5/2`.

AI-written Lean code, Claude, 2026-11-23. Binary Goldbach is OPEN.
-/
import LeanLab.DensityGoldbach.Decomp408b
import LeanLab.DensityGoldbach.U1494Spec

open Finset
open scoped Classical

noncomputable section

namespace LeanLab.DensityGoldbach.Decomp408b

open LeanLab.DensityGoldbach.U1446 LeanLab.DensityGoldbach.U1494

/-- LEAF: Green math/0302311 Section 6, proof of Lemma 6.6, the Bourgain large spectrum
estimate `#{r : |f^(r)| ≥ δ} ≪_ε δ^{-2-ε}` for `0 ≤ f ≤ ν_b`, taken at `ε = 1/4`, and only in
the middle window `δ < δ₀` above the Parseval line. Class HARD: it needs the enveloping sieve
majorant, or a moment of the Ramanujan majorant higher than the eighth used in `U1502Core`. -/
theorem large_spectrum_mid_nine_quarters :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ K : ℝ, 0 < K ∧ ∃ z₁ : ℕ, ∀ z : ℕ, z₁ ≤ z →
      ∀ b : ℕ, b < primorial z → Nat.Coprime b (primorial z) → ∃ N₀ : ℕ, ∀ N : ℕ, ∀ [NeZero N],
        N.Prime → N₀ ≤ N → ∀ f : ZMod N → ℝ, (∀ n, 0 ≤ f n ∧ f n ≤ nuW (primorial z) b N n) →
          ∀ δ : ℝ, 0 < δ → δ < δ₀ →
            K * δ ^ (-(9 / 4 : ℝ)) < 2 * Real.log ((primorial z : ℝ) * N) * δ ^ (-(2 : ℝ)) →
            ((univ.filter (fun r => δ ≤ ‖hatE N f r‖)).card : ℝ) ≤ K * δ ^ (-(9 / 4 : ℝ)) := by
  sorry

/-- The large spectrum bound at exponent `9/4` for all levels `δ < δ₀`: Parseval handles the
levels below the Parseval line. Same proof as `U1494.small_of_mid`. -/
theorem small_nine_quarters :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ K : ℝ, 0 < K ∧ ∃ z₁ : ℕ, ∀ z : ℕ, z₁ ≤ z →
      ∀ b : ℕ, b < primorial z → Nat.Coprime b (primorial z) → ∃ N₀ : ℕ, ∀ N : ℕ, ∀ [NeZero N],
        N.Prime → N₀ ≤ N → ∀ f : ZMod N → ℝ, (∀ n, 0 ≤ f n ∧ f n ≤ nuW (primorial z) b N n) →
          ∀ δ : ℝ, 0 < δ → δ < δ₀ →
            ((univ.filter (fun r => δ ≤ ‖hatE N f r‖)).card : ℝ) ≤ K * δ ^ (-(9 / 4 : ℝ)) := by
  obtain ⟨δ₀, hδ₀, K, hK, z₁, hG⟩ := large_spectrum_mid_nine_quarters
  refine ⟨δ₀, hδ₀, K, hK, z₁, fun z hz b hb hcop => ?_⟩
  obtain ⟨Na, hNa⟩ := hG z hz b hb hcop
  obtain ⟨Nc, hNc⟩ := nu_avg_close (primorial z) b hb hcop 1 one_pos
  refine ⟨max Na Nc, fun N _ hNp hN f hf δ hδ hδ₀' => ?_⟩
  set ν := nuW (primorial z) b N
  set L := Real.log ((primorial z : ℝ) * N)
  rcases lt_or_ge (K * δ ^ (-(9 / 4 : ℝ))) (2 * L * δ ^ (-(2 : ℝ))) with hw | hp
  · exact hNa N hNp (le_of_max_le_left hN) f hf δ hδ hδ₀' hw
  · have hA : avg N ν ≤ 2 := by
      have := hNc N (le_of_max_le_right hN)
      linarith [(abs_le.1 this).2]
    have hc := parseval_count f ν hf L (nuW_le_log _ b N hb) δ hδ
    have hd2 : δ ^ (-(2 : ℝ)) = (δ ^ 2)⁻¹ := by
      rw [Real.rpow_neg hδ.le]; norm_cast
    have hδ2 : 0 < δ ^ 2 := by positivity
    have hL0 : 0 ≤ L := (nuW_nonneg _ _ _ 0).trans (nuW_le_log _ b N hb 0)
    have : ((univ.filter (fun r => δ ≤ ‖hatE N f r‖)).card : ℝ) ≤ 2 * L * δ ^ (-(2 : ℝ)) := by
      rw [hd2, ← div_eq_mul_inv, le_div_iff₀ hδ2]
      nlinarith
    linarith

/-- The large spectrum bound at exponent `9/4` at every level: TT* with `U1484.green62` handles
the levels `δ ≥ δ₀`. Same proof as `U1494.largeSpec_of_small`. -/
theorem largeSpec_nine_quarters :
    ∃ K : ℝ, 0 < K ∧ ∃ z₁ : ℕ, ∀ z : ℕ, z₁ ≤ z → ∀ b : ℕ,
      b < primorial z → Nat.Coprime b (primorial z) → ∃ N₀ : ℕ, ∀ N : ℕ, ∀ [NeZero N],
        N.Prime → N₀ ≤ N → ∀ f : ZMod N → ℝ, (∀ n, 0 ≤ f n ∧ f n ≤ nuW (primorial z) b N n) →
          ∀ δ : ℝ, 0 < δ →
            ((univ.filter (fun r => δ ≤ ‖hatE N f r‖)).card : ℝ) ≤ K * δ ^ (-(9 / 4 : ℝ)) := by
  obtain ⟨δ₀, hδ₀, K, hK, z₁, hG⟩ := small_nine_quarters
  set q : ℝ := 9 / 4 with hqdef
  have hq : 0 < q := by norm_num [hqdef]
  set c : ℝ := δ₀ ^ 2 / 4 with hcdef
  have hc : 0 < c := by positivity
  obtain ⟨z₀, hz₀⟩ := LeanLab.DensityGoldbach.U1484.green62 c hc
  set K' : ℝ := K + 8 * 2 ^ q / δ₀ ^ 2
  have hK' : 0 < K' := by positivity
  refine ⟨K', hK', max z₁ z₀, fun z hz b hb hcop => ?_⟩
  obtain ⟨Na, hNa⟩ := hG z (le_of_max_le_left hz) b hb hcop
  obtain ⟨Nb, hNb⟩ := hz₀ z (le_of_max_le_right hz) b hb hcop
  obtain ⟨Nc, hNc⟩ := nu_avg_close (primorial z) b hb hcop 1 one_pos
  refine ⟨max Na (max Nb Nc), fun N _ hNp hN f hf δ hδ => ?_⟩
  set ν := nuW (primorial z) b N
  have hA : avg N ν ≤ 2 := by
    have := hNc N (le_of_max_le_right (le_of_max_le_right hN))
    linarith [(abs_le.1 this).2]
  have hqpos : 0 < δ ^ (-q) := Real.rpow_pos_of_pos hδ _
  set S := univ.filter (fun r : ZMod N => δ ≤ ‖hatE N f r‖)
  rcases lt_or_ge δ δ₀ with hsm | hlg
  · have := hNa N hNp (le_of_max_le_left hN) f hf δ hδ hsm
    have : K * δ ^ (-q) ≤ K' * δ ^ (-q) := by
      apply mul_le_mul_of_nonneg_right _ hqpos.le
      simp only [K']; have : 0 ≤ 8 * 2 ^ q / δ₀ ^ 2 := by positivity
      linarith
    linarith
  rcases lt_or_ge 2 δ with hbig | hmid
  · have hS : S.card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro r _ hr
      have h1 := LeanLab.DensityGoldbach.U1467.norm_hatE_le f (fun n => (hf n).1) r
      have h2 := LeanLab.DensityGoldbach.U1467.avg_mono f ν (fun n => (hf n).2)
      linarith
    rw [hS, Nat.cast_zero]; positivity
  · have hcnt := tt_star_count f ν hf 2 c hA hc.le
      (fun s hs => hNb N hNp (le_of_max_le_left (le_of_max_le_right hN)) s hs) δ hδ
      (by
        have : δ₀ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hδ₀.le hlg 2
        simp only [hcdef]; linarith)
      S (fun r hr => (mem_filter.1 hr).2)
    have hS8 : (S.card : ℝ) ≤ 8 / δ₀ ^ 2 := by
      have h2 : δ₀ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hδ₀.le hlg 2
      rw [le_div_iff₀ (by positivity)]
      have : (S.card : ℝ) * δ₀ ^ 2 ≤ (S.card : ℝ) * δ ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
      linarith
    have hone : 1 ≤ 2 ^ q * δ ^ (-q) := by
      rw [Real.rpow_neg hδ.le, ← div_eq_mul_inv, ← Real.div_rpow zero_le_two hδ.le]
      exact Real.one_le_rpow (by rw [le_div_iff₀ hδ]; linarith) hq.le
    have : 8 / δ₀ ^ 2 ≤ K' * δ ^ (-q) := by
      have e : 8 / δ₀ ^ 2 * (2 ^ q * δ ^ (-q)) = 8 * 2 ^ q / δ₀ ^ 2 * δ ^ (-q) := by ring
      have h1 : 8 / δ₀ ^ 2 ≤ 8 / δ₀ ^ 2 * (2 ^ q * δ ^ (-q)) :=
        le_mul_of_one_le_right (by positivity) hone
      have h2 : 8 * 2 ^ q / δ₀ ^ 2 * δ ^ (-q) ≤ K' * δ ^ (-q) := by
        apply mul_le_mul_of_nonneg_right _ hqpos.le
        simp only [K']; linarith
      linarith
    linarith

/-- Split of `restriction_five_halves`: the dyadic summation `U1488.dyadic_sum` with the weak
exponent `9/4` below the strong exponent `5/2`, from `largeSpec_nine_quarters`. -/
theorem restriction_five_halves_split : U1488.Green66p (5 / 2) := by
  obtain ⟨K, hK, z₁, hG⟩ := largeSpec_nine_quarters
  set q : ℝ := 9 / 4 with hqdef
  set p : ℝ := 5 / 2 with hpdef
  have hq : 0 < q := by norm_num [hqdef]
  have hqp : q < p := by norm_num [hqdef, hpdef]
  have hp0 : 0 < p := by norm_num [hpdef]
  set B := 1 + K * 2 ^ q * (K ^ (1 / q)) ^ (p - q) / (1 - (1 / 2 : ℝ) ^ (p - q))
  have hρ1 : (1 / 2 : ℝ) ^ (p - q) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  have hB : 0 < B := by
    have : 0 < 1 - (1 / 2 : ℝ) ^ (p - q) := by linarith
    positivity
  refine ⟨B ^ (1 / p), by positivity, z₁, fun z hz b hb hcop => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hG z hz b hb hcop
  refine ⟨N₀, fun N _ hNp hN f hf => ?_⟩
  have hs := U1488.dyadic_sum (fun r => ‖hatE N f r‖) (fun r => norm_nonneg _) q p K hq hqp hK
    (hN₀ N hNp hN f hf)
  unfold lpHat
  exact Real.rpow_le_rpow (sum_nonneg fun r _ => by positivity) hs (by positivity)

end LeanLab.DensityGoldbach.Decomp408b
