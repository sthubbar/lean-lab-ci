import LeanLab.Halupczok2012.Split398aMajorE2

/-!
Closing tools for leaf `Split398aMajorA7.e2_twisted_partial_summation`, PP1993 page 46
display 12. Source: A. Perelli and J. Pintz, J. London Math. Soc. 47, 1993, pages 41 to 49.
Round 4 proves `log_pow_le_rpow`, `short_tail_absorb`, `deltaChi_norm_le`, `long_tail_le`
and `tail_le`, and with them closes the leaf: `e2_twisted_partial_summation_proved` has exactly
the statement of `Split398aMajorA7.e2_twisted_partial_summation`, from ShortSW only. Tails of
length at least N to the 7/12 + eps/2 use ShortSW at eps/2; shorter tails use the trivial
bound, absorbed since Y is at least N to the 7/12 + eps. `a7_from_e1` assembles
`Split398aMajor.a7_R1_sup`, as `A7Stmt`, from ShortSW and the leaf `e1_expansion` alone.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Split398aMajorE2Close

/-- Proved: for delta positive and any real c, log N to the c is eventually at most N to the
delta. -/
theorem log_pow_le_rpow (δ c : ℝ) (hδ : 0 < δ) :
    ∃ N0 : ℝ, ∀ N : ℝ, N0 ≤ N → Real.log N ^ c ≤ N ^ δ := by
  have h := (isLittleO_log_rpow_rpow_atTop c hδ).bound one_pos
  rw [Filter.eventually_atTop] at h
  obtain ⟨N0, hN0⟩ := h
  refine ⟨max N0 (Real.exp 1), fun N hN => ?_⟩
  have hN1 : Real.exp 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hN1
  have hlog : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hN1
  have := hN0 N (le_trans (le_max_left _ _) hN)
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
    Real.norm_of_nonneg (Real.rpow_nonneg hNpos.le _)] at this
  exact this

/-- Proved: the absorption of a short tail. For eps and C' positive there is N0 such that for
N at least N0, Y at least N to the 7/12 + eps and a tail length R at most N to the
7/12 + eps/2, R + 1 times log N + 1 is at most 4 Y times log N to the minus C'. -/
theorem short_tail_absorb (ε C' : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℝ, ∀ N Y R : ℝ, N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → 0 ≤ R →
      R ≤ N ^ (7 / 12 + ε / 2) →
      (R + 1) * (Real.log N + 1) ≤ 4 * (Y * Real.log N ^ (-C')) := by
  obtain ⟨N1, hN1⟩ := log_pow_le_rpow (ε / 2) (C' + 1) (by linarith)
  refine ⟨max N1 (Real.exp 1), fun N Y R hN hY hR0 hR => ?_⟩
  have hNe : Real.exp 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hNe
  have hN1' : 1 ≤ N := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hNe
  have hlog : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hNe
  have hL := hN1 N (le_trans (le_max_left _ _) hN)
  set L := Real.log N with hLdef
  have hLpos : 0 < L := by linarith
  -- N^(7/12+eps/2) >= 1
  have hP1 : 1 ≤ N ^ (7 / 12 + ε / 2) := Real.one_le_rpow hN1' (by linarith)
  have hsplit : N ^ (7 / 12 + ε) = N ^ (7 / 12 + ε / 2) * N ^ (ε / 2) := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have hLC : L ^ (C' + 1) = L ^ C' * L := by
    rw [Real.rpow_add hLpos, Real.rpow_one]
  have hLneg : L ^ (-C') * L ^ C' = 1 := by
    rw [← Real.rpow_add hLpos]; simp
  have hLCpos : 0 < L ^ C' := Real.rpow_pos_of_pos hLpos _
  have hLnegpos : 0 < L ^ (-C') := Real.rpow_pos_of_pos hLpos _
  -- (R+1)(L+1) <= 2P * 2L = 4 P L ; need 4 P L <= Y L^{-C'}
  -- Y L^{-C'} >= P N^{eps/2} L^{-C'} >= P L^{C'+1} L^{-C'} = P L
  have hstep : N ^ (7 / 12 + ε / 2) * L ≤ Y * L ^ (-C') := by
    calc N ^ (7 / 12 + ε / 2) * L = N ^ (7 / 12 + ε / 2) * L ^ (C' + 1) * L ^ (-C') := by
          rw [hLC]; field_simp; nlinarith [hLneg]
      _ ≤ N ^ (7 / 12 + ε / 2) * N ^ (ε / 2) * L ^ (-C') := by
          gcongr
      _ ≤ Y * L ^ (-C') := by rw [← hsplit]; gcongr
  have hR1 : R + 1 ≤ 2 * N ^ (7 / 12 + ε / 2) := by linarith
  have hL1 : L + 1 ≤ 2 * L := by linarith
  calc (R + 1) * (L + 1) ≤ (2 * N ^ (7 / 12 + ε / 2)) * (2 * L) := by
        apply mul_le_mul hR1 hL1 (by linarith) (by linarith)
    _ = 4 * (N ^ (7 / 12 + ε / 2) * L) := by ring
    _ ≤ 4 * (Y * L ^ (-C')) := by linarith

/-- Proved: delta_chi has norm at most 1. -/
theorem deltaChi_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ‖LeanLab.Halupczok2012.Split398aMajor.deltaChi χ‖ ≤ 1 := by
  unfold LeanLab.Halupczok2012.Split398aMajor.deltaChi
  split_ifs <;> simp

/-- Proved: the long tail step of display 12 from ShortSW. Given display 6, for eps, D and C'
positive there are K and N0 such that every tail kRange (N - R) R with N to the 7/12 + eps at
most R at most N and 1 at most q at most L^D has twisted free sum of Lambda chi minus delta_chi
at most K R L^{-C'} + 1. -/
theorem long_tail_le (h6 : LeanLab.Halupczok2012.Split398aMajor.ShortSW) (ε D C' : ℝ)
    (hε : 0 < ε) (hD : 0 < D) (hC : 0 < C') :
    ∃ K N0 : ℝ, ∀ N R : ℝ, ∀ q : ℕ, ∀ χ : DirichletCharacter ℂ q,
      N0 ≤ N → N ^ (7 / 12 + ε) ≤ R → R ≤ N → 1 ≤ q → (q : ℝ) ≤ Real.log N ^ D →
      ‖∑ n ∈ LeanLab.Halupczok2012.kRange (N - R) R,
          ((ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) -
            LeanLab.Halupczok2012.Split398aMajor.deltaChi χ)‖ ≤
        K * R * Real.log N ^ (-C') + 1 := by
  obtain ⟨K, N0, hK⟩ := h6 ε D C' hε hD hC
  refine ⟨K, max N0 1, fun N R q χ hN hR hRN hq hqD => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hR0 : 0 ≤ R := le_trans (Real.rpow_nonneg (by linarith) _) hR
  have hX : 0 ≤ N - R := by linarith
  have hc := LeanLab.Halupczok2012.Split398aMajorE2.sum_sub_const_close (N - R) R hX hR0
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q))
    (LeanLab.Halupczok2012.Split398aMajor.deltaChi χ) (deltaChi_norm_le χ)
  have hS := hK N R q χ (le_trans (le_max_left _ _) hN) hR hRN hq hqD
  have := norm_sub_norm_le
    (∑ n ∈ LeanLab.Halupczok2012.kRange (N - R) R,
      ((ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) -
        LeanLab.Halupczok2012.Split398aMajor.deltaChi χ))
    ((∑ n ∈ LeanLab.Halupczok2012.kRange (N - R) R,
      (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) -
        LeanLab.Halupczok2012.Split398aMajor.deltaChi χ * (R : ℂ))
  linarith

/-- Proved: every tail of display 12. Given display 6, for eps, D and C' positive there are K
and N0 such that for N at least N0, Y at least N to the 7/12 + eps, 1 at most q at most L^D
and a real t with 0 at most t at most N and N - t at most 2 Y, the tail sum over kRange t of
N - t of Lambda chi minus delta_chi is at most K Y L^{-C'} + 1: ShortSW at eps/2 for tails of
length at least N to the 7/12 + eps/2, the trivial bound with `short_tail_absorb` below. -/
theorem tail_le (h6 : LeanLab.Halupczok2012.Split398aMajor.ShortSW) (ε D C' : ℝ)
    (hε : 0 < ε) (hD : 0 < D) (hC : 0 < C') :
    ∃ K N0 : ℝ, ∀ N Y t : ℝ, ∀ q : ℕ, ∀ χ : DirichletCharacter ℂ q,
      N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → 1 ≤ q → (q : ℝ) ≤ Real.log N ^ D →
      0 ≤ t → t ≤ N → N - t ≤ 2 * Y →
      ‖∑ n ∈ LeanLab.Halupczok2012.kRange t (N - t),
          ((ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) -
            LeanLab.Halupczok2012.Split398aMajor.deltaChi χ)‖ ≤
        K * Y * Real.log N ^ (-C') + 1 := by
  obtain ⟨K, N1, hK⟩ := long_tail_le h6 (ε / 2) D C' (by linarith) hD hC
  obtain ⟨N2, hN2⟩ := short_tail_absorb ε C' hε
  refine ⟨2 * max K 0 + 4, max (max N1 N2) 1, fun N Y t q χ hN hY hq hqD ht0 htN htY => ?_⟩
  have hN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2' : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNone : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hLpos : 0 ≤ Real.log N ^ (-C') := Real.rpow_nonneg (Real.log_nonneg hNone) _
  have hY0 : 0 ≤ Y := le_trans (Real.rpow_nonneg (by linarith) _) hY
  have hYL : 0 ≤ Y * Real.log N ^ (-C') := mul_nonneg hY0 hLpos
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  by_cases hlong : N ^ (7 / 12 + ε / 2) ≤ N - t
  · have h := hK N (N - t) q χ hN1 hlong (by linarith) hq hqD
    rw [sub_sub_cancel] at h
    have h2 : K * (N - t) * Real.log N ^ (-C') ≤ max K 0 * (2 * Y) * Real.log N ^ (-C') := by
      apply mul_le_mul_of_nonneg_right _ hLpos
      exact mul_le_mul (le_max_left _ _) htY (by linarith) hK0
    nlinarith
  · push_neg at hlong
    have h := LeanLab.Halupczok2012.Split398aMajorE2.short_segment_le χ t (N - t) ht0
      (by linarith) (by linarith)
    rw [add_sub_cancel] at h
    have h2 := hN2 N Y (N - t) hN2' hY (by linarith) hlong.le
    nlinarith

open Finset in
open scoped Classical ArithmeticFunction.vonMangoldt in
open LeanLab.Halupczok2012 LeanLab.Halupczok2012.Decomp398a
  LeanLab.Halupczok2012.Split398aMajor in
/-- Proved: the leaf `Split398aMajorA7.e2_twisted_partial_summation`, PP1993 p. 46 display 12,
with exactly its statement, from ShortSW: partial summation with `twisted_kRange_le`, the
initial segments through `segments_le` and `tail_le`, the count through `count_eta_le`. -/
theorem e2_twisted_partial_summation_proved (h6 : ShortSW) :
    ∀ ε A C' : ℝ, 0 < ε → 0 < A → 0 < C' → ∃ K N0 : ℝ, ∀ N Y η : ℝ, ∀ (q : ℕ) [NeZero q],
    ∀ χ : DirichletCharacter ℂ q,
    N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N → q ∈ majorQ N ε A → η ∈ xiArc N Y ε A q →
    ‖∑ n ∈ kRange (N - Y) Y, ((Λ n : ℂ) * χ (n : ZMod q) - deltaChi χ) *
        phase ((n : ℝ) * η)‖ ≤ K * Y * Real.log N ^ (2 * bigB ε A - C') := by
  intro ε A C' hε hA hC
  have hB : 0 < bigB ε A := by unfold bigB; positivity
  obtain ⟨K1, N1, hK1⟩ := tail_le h6 ε (bigB ε A) C' hε hB hC
  obtain ⟨N3, hN3⟩ := log_pow_le_rpow ε C' hε
  refine ⟨2 * (|K1| + 1) * (1 + 4 * Real.pi), max (max N1 N3) (Real.exp 1),
    fun N Y η q _ χ hN hY hYN hq hη => ?_⟩
  have hN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN3' : N3 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNe : Real.exp 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNone : 1 ≤ N := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hNe
  have hNpos : 0 < N := by linarith
  have hlog : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hNe
  set L := Real.log N with hLdef
  have hLpos : 0 < L := by linarith
  have hY1 : 1 ≤ Y := le_trans (Real.one_le_rpow hNone (by linarith)) hY
  have hqmem := hq
  unfold majorQ at hqmem
  rw [Finset.mem_Icc] at hqmem
  have hq1 : 1 ≤ q := hqmem.1
  have hqD : (q : ℝ) ≤ L ^ bigB ε A :=
    le_trans (by exact_mod_cast hqmem.2) (Nat.floor_le (Real.rpow_nonneg hLpos.le _))
  -- Y L^{-C'} >= 1
  have hLC : L ^ C' ≤ Y := by
    refine le_trans (hN3 N hN3') (le_trans ?_ hY)
    exact Real.rpow_le_rpow_of_exponent_le hNone (by linarith)
  have hLneg : L ^ (-C') * L ^ C' = 1 := by
    rw [← Real.rpow_add hLpos]; simp
  have hLnegpos : 0 < L ^ (-C') := Real.rpow_pos_of_pos hLpos _
  have hYL1 : 1 ≤ Y * L ^ (-C') := by nlinarith
  set M := K1 * Y * L ^ (-C') + 1 with hM
  have hMle : M ≤ (|K1| + 1) * (Y * L ^ (-C')) := by
    have : K1 * Y * L ^ (-C') ≤ |K1| * (Y * L ^ (-C')) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    nlinarith
  have hX : 0 ≤ N - Y := by linarith
  have hR : (0 : ℝ) ≤ Y := by linarith
  have hXR : N - Y + Y = N := by ring
  set f : ℕ → ℂ := fun n => (Λ n : ℂ) * χ (n : ZMod q) - deltaChi χ with hf
  have hF : ‖∑ n ∈ kRange (N - Y) Y, f n‖ ≤ M := by
    have h := hK1 N Y (N - Y) q χ hN1 hY hq1 hqD hX (by linarith) (by linarith)
    rw [sub_sub_cancel] at h
    exact h
  have hT : ∀ t : ℕ, ⌊N - Y⌋₊ ≤ t → t ≤ ⌊N - Y + Y⌋₊ →
      ‖∑ n ∈ kRange (t : ℝ) (N - Y + Y - t), f n‖ ≤ M := by
    intro t ht1 ht2
    rw [hXR] at ht2 ⊢
    have htN : (t : ℝ) ≤ N := le_trans (by exact_mod_cast ht2) (Nat.floor_le hNpos.le)
    have htX : N - Y - 1 < (t : ℝ) :=
      lt_of_lt_of_le (Nat.sub_one_lt_floor _) (by exact_mod_cast ht1)
    exact hK1 N Y t q χ hN1 hY hq1 hqD (Nat.cast_nonneg _) htN (by linarith)
  have hseg := LeanLab.Halupczok2012.Split398aMajorE2.segments_le (N - Y) Y M hX hR f hF hT
  have htw := LeanLab.Halupczok2012.Split398aMajorE2.twisted_kRange_le (N - Y) Y η (2 * M)
    hX hR f hseg
  have hcnt := LeanLab.Halupczok2012.Split398aMajorE2.count_eta_le N Y ε A η q hq1 hY1 hη
  have hL2B : 1 ≤ L ^ (2 * bigB ε A) := Real.one_le_rpow hlog (by linarith)
  have hqpos : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hdiv : L ^ (2 * bigB ε A) / q ≤ L ^ (2 * bigB ε A) :=
    div_le_self (by linarith) hqpos
  have hfac : 1 + (Y + 1) * (2 * Real.pi * |η|) ≤ (1 + 4 * Real.pi) * L ^ (2 * bigB ε A) := by
    have : (Y + 1) * (2 * Real.pi * |η|) = 2 * Real.pi * ((Y + 1) * |η|) := by ring
    rw [this]
    have hpi := Real.pi_pos
    nlinarith
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hF
  have hsplit : L ^ (2 * bigB ε A - C') = L ^ (-C') * L ^ (2 * bigB ε A) := by
    rw [← Real.rpow_add hLpos]; ring_nf
  calc ‖∑ n ∈ kRange (N - Y) Y, f n * phase ((n : ℝ) * η)‖
      ≤ 2 * M * (1 + (Y + 1) * (2 * Real.pi * |η|)) := htw
    _ ≤ 2 * ((|K1| + 1) * (Y * L ^ (-C'))) * ((1 + 4 * Real.pi) * L ^ (2 * bigB ε A)) := by
        apply mul_le_mul (by linarith) hfac (by positivity) (by positivity)
    _ = 2 * (|K1| + 1) * (1 + 4 * Real.pi) * Y * L ^ (2 * bigB ε A - C') := by
        rw [hsplit]; ring

open Finset in
open scoped Classical ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius in
open LeanLab.Halupczok2012 LeanLab.Halupczok2012.Decomp398a
  LeanLab.Halupczok2012.Split398aMajor LeanLab.Halupczok2012.Split398aMajorA7 in
/-- Proved: the assembly of `Split398aMajor.a7_R1_sup` from ShortSW and the single leaf
`e1_expansion`, taken as the hypothesis he1 with exactly its statement; the e2 leaf is
replaced by `e2_twisted_partial_summation_proved`. -/
theorem a7_from_e1 (h6 : ShortSW) (he1 : ∀ N Y η : ℝ, ∀ (q : ℕ) [NeZero q], ∀ a : ℕ,
    a.Coprime q → (q : ℝ) ≤ N → 2 ≤ N →
    ‖firstR N Y q a η - (1 / (Nat.totient q : ℂ)) *
        ∑ᶠ χ : DirichletCharacter ℂ q, χ (a : ZMod q) *
          (∑ b : ZMod q, (starRingEnd ℂ) (χ b) * phase ((b.val : ℝ) / q)) *
          ∑ n ∈ kRange (N - Y) Y, ((Λ n : ℂ) * χ (n : ZMod q) - deltaChi χ) *
            phase ((n : ℝ) * η)‖ ≤ 2 * Real.log N ^ 2) : A7Stmt := by
  intro ε A C' hε hA hC'
  have hB : 0 < bigB ε A := by unfold bigB; positivity
  set B := bigB ε A with hBdef
  obtain ⟨K, N1, hK⟩ := e2_twisted_partial_summation_proved h6 ε A (C' + B) hε hA (by linarith)
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp
    (((log_rpow_le_eventually (2 + C' - 2 * B) (show (0 : ℝ) < 7 / 12 by norm_num)
      (show (0 : ℝ) < 1 / 2 by norm_num)).and
    (log_rpow_le_eventually B (show (0 : ℝ) < 1 by norm_num)
      (show (0 : ℝ) < 1 by norm_num))).and (Filter.eventually_ge_atTop (max N1 3)))
  refine ⟨max K 0 + 1, N0, ?_⟩
  intro N Y q a η hN hlow hYN hq ha hη
  obtain ⟨⟨c1, c2⟩, hN3⟩ := hN0 N hN
  have hN1 : N1 ≤ N := (le_max_left _ _).trans hN3
  have hN3' : 3 ≤ N := (le_max_right _ _).trans hN3
  have hNpos : 0 < N := by linarith
  have hL0 : 0 < Real.log N := Real.log_pos (by linarith)
  set L := Real.log N with hLdef
  have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
  haveI : NeZero q := ⟨by omega⟩
  have hqL : (q : ℝ) ≤ L ^ B := by
    have h := (mem_Icc.mp hq).2
    exact (Nat.le_floor_iff (Real.rpow_nonneg hL0.le _)).mp h
  have hqN : (q : ℝ) ≤ N := by
    rw [Real.rpow_one, one_mul] at c2
    linarith
  have haq : a.Coprime q := (mem_filter.mp ha).2
  have hP1 : 1 ≤ N ^ ((7 : ℝ) / 12) := Real.one_le_rpow (by linarith) (by norm_num)
  have hPY : N ^ ((7 : ℝ) / 12) ≤ Y :=
    (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)).trans hlow
  have hY0 : 0 < Y := by linarith
  have hE1 := he1 N Y η q a haq hqN (by linarith)
  have hT : ∀ χ : DirichletCharacter ℂ q,
      ‖∑ n ∈ kRange (N - Y) Y, ((Λ n : ℂ) * χ (n : ZMod q) - deltaChi χ) *
        phase ((n : ℝ) * η)‖ ≤ max K 0 * Y * L ^ (2 * B - (C' + B)) := fun χ =>
    (hK N Y η q χ hN1 hlow hYN hq hη).trans
      (by gcongr; exact le_max_left _ _)
  have hE3 := charsum_bound q a _ _ hT
  have hpow : (q : ℝ) * (max K 0 * Y * L ^ (2 * B - (C' + B))) ≤
      max K 0 * Y * L ^ (2 * B - C') := by
    have e : L ^ (2 * B - C') = L ^ B * L ^ (2 * B - (C' + B)) := by
      rw [← Real.rpow_add hL0]; ring_nf
    rw [e]
    have : 0 ≤ max K 0 * Y * L ^ (2 * B - (C' + B)) := by positivity
    nlinarith [le_max_right K 0, Real.rpow_nonneg hL0.le (2 * B - (C' + B))]
  have hcorr : 2 * L ^ 2 ≤ Y * L ^ (2 * B - C') := by
    have e : L ^ (2 : ℕ) = L ^ (2 + C' - 2 * B) * L ^ (2 * B - C') := by
      rw [← Real.rpow_add hL0, ← Real.rpow_natCast]; ring_nf
    rw [e]
    have hp : 0 < L ^ (2 * B - C') := Real.rpow_pos_of_pos hL0 _
    nlinarith
  calc ‖firstR N Y q a η‖ ≤ ‖firstR N Y q a η - (1 / (Nat.totient q : ℂ)) *
        ∑ᶠ χ : DirichletCharacter ℂ q, χ (a : ZMod q) *
          (∑ b : ZMod q, (starRingEnd ℂ) (χ b) * phase ((b.val : ℝ) / q)) *
          ∑ n ∈ kRange (N - Y) Y, ((Λ n : ℂ) * χ (n : ZMod q) - deltaChi χ) *
            phase ((n : ℝ) * η)‖ + ‖(1 / (Nat.totient q : ℂ)) *
        ∑ᶠ χ : DirichletCharacter ℂ q, χ (a : ZMod q) *
          (∑ b : ZMod q, (starRingEnd ℂ) (χ b) * phase ((b.val : ℝ) / q)) *
          ∑ n ∈ kRange (N - Y) Y, ((Λ n : ℂ) * χ (n : ZMod q) - deltaChi χ) *
            phase ((n : ℝ) * η)‖ := norm_le_norm_sub_add _ _
    _ ≤ 2 * L ^ 2 + max K 0 * Y * L ^ (2 * B - C') := add_le_add hE1 (hE3.trans hpow)
    _ ≤ (max K 0 + 1) * Y * L ^ (2 * B - C') := by nlinarith

end LeanLab.Halupczok2012.Split398aMajorE2Close
