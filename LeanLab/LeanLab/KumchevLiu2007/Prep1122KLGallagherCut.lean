/-
BURST 2026-11-22 S35, unit P1122-0137. SPLIT of the LEAF
Prep1121DKLMajorCut.S2_sub_S2star_major_mean_square, the mean square of S2 - S2*
over the major arcs M. Kumchev and Liu 2007, P0088, arXiv 0801.0130, page 5
displays 15, 18 and 19 and page 6 display 20.

The printed argument, with Y = windowY X eps, P = (log X)^B and Q = H/P:
* page 4 display 15: the arcs M(q, a) are disjoint, so on the arc of q, a the
  function S2* is the single term S(q, a)/phi(q) T2(beta), beta = alpha - a/q.
  LEAF arc_localization, MEDIUM.
* page 5 display 18: (A2.1) puts the rough weight on m coprime to q, and the
  orthogonality of the characters modulo q bounds |S2 - S2*|^2 by the sum over
  chi of |W2(beta, chi)|^2. LEAF char_orthogonality_18, MEDIUM.
* page 6 before display 20: Gallagher's lemma, reference 5 Lemma 1, with the
  device of Saffari and Vaughan, reference 21 page 25, bounds the integral of
  |W2|^2 over |beta| at most 1/(qQ) by (qQ)^(-2) times the mean square of
  (A2.2) plus delta, for some delta of size qQ/Y. LEAF
  gallagher_saffari_vaughan, HARD, a citation wall.
* hypothesis (A2.2), here A22Corr, then gives C P^(-4) for each chi; this
  combination is PROVED below as arc_char_mean_square.
* at most P characters and at most 2 P^2 arcs give C P^(-1), at most
  C P^(-1/2) as the parent states. PROVED below.

The final theorem S2_sub_S2star_major_mean_square_of_pieces proves the exact
statement of the parent leaf from the pieces, CONDITIONAL ON A22Corr, the
cited hypothesis (A2.2) of page 5. W2(beta, chi) of page 5 is written out in
each statement, with chi on the weight only as in A22Corr, so no new
definition is made.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1121DKLMajorCut

namespace LeanLab.KumchevLiu2007.Prep1122KLGallagherCut

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Prep1121KLMajor
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-! ## The leaves -/

/-- LEAF: P0088 page 5 display 18, orthogonality of the characters modulo q. Class MEDIUM.
Let alpha = a/q + beta with a coprime to q. When every m of the square window with a
nonzero rough weight is coprime to q, which is (A2.1) of page 4 as the paper notes
before display 18, expanding e(a m^2/q) over the characters modulo q writes
S2(alpha) - S(q, a)/phi(q) T2(beta) as phi(q)^(-1) times the sum over chi of the
twisted Gauss sum of conj chi times W2(beta, chi). Cauchy's inequality and Parseval
over the characters, which give phi(q)^2 for the Gauss sums, then bound
|S2 - S2*|^2 by the sum of |W2(beta, chi)|^2. W2 of page 5 is written out with chi
on the weight only, the form of A22Corr. -/
theorem char_orthogonality_18 (Y P : ℝ) (q a : ℕ) (hq : 1 ≤ q) (ha : Nat.Coprime a q)
    (hcop : ∀ m : ℕ, roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m ≠ 0 → Nat.Coprime m q)
    (β : ℝ) :
    ‖roughSum Y P ((a : ℝ) / q + β) - U1534.gaussS q a / (Nat.totient q : ℂ) * T2 Y P β‖ ^ 2 ≤
      ∑ χ : DirichletCharacter ℂ q,
        ‖∑ m ∈ squareWindow Y,
          (roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m * χ m -
            (if χ = 1 then ((Task556a.f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ)
             else 0)) * fourier ((m ^ 2 : ℕ) : ℤ) (β : AddCircle (1 : ℝ))‖ ^ 2 := by
  sorry

/-- LEAF: P0088 page 4 display 15 and page 5 the definition of S2* on M. Class MEDIUM.
For X large in the block range, H/P exceeds 2P, so the closed arcs M(q, a) with q at
most P are disjoint, and every alpha of the period interval in M lies on the arc of
one pair of arcPairs P, with a from 0 to q. On that arc S2* is the single term
S(q, a)/phi(q) T2(alpha - a/q), and the substitution alpha = a/q + beta carries the
arc to |beta| at most 1/(qQ), Q = H/P. So the mean square over M is at most the sum
over the arcs of the mean squares in beta, the step from display 16 to display 19. -/
theorem arc_localization :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ X0 : ℝ, ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        (∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs H (Real.log X ^ B),
          ‖roughSum (windowY X ε) (Real.log X ^ B) α -
            S2star (windowY X ε) H (Real.log X ^ B) α‖ ^ 2) ≤
          ∑ v ∈ arcPairs (Real.log X ^ B),
            ∫ β in -((v.1 : ℝ) * (H / Real.log X ^ B))⁻¹..((v.1 : ℝ) * (H / Real.log X ^ B))⁻¹,
              ‖roughSum (windowY X ε) (Real.log X ^ B) ((v.2 : ℝ) / v.1 + β) -
                U1534.gaussS v.1 v.2 / (Nat.totient v.1 : ℂ) *
                  T2 (windowY X ε) (Real.log X ^ B) β‖ ^ 2 := by
  sorry

/-- LEAF: P0088 page 6, the display before display 20: Gallagher's lemma, reference 5
Lemma 1, combined with the device of Saffari and Vaughan, reference 21 page 25.
Class HARD, a citation wall: neither proof is printed in P0088. For each modulus q at
most P and each character chi modulo q there is delta of size qQ/Y, Q = H/P, at most
qQ/Y as (A2.2) requires, such that the integral of |W2(beta, chi)|^2 over |beta| at
most 1/(qQ) is at most a constant times (qQ)^(-2) times the mean square over
Y/4 < t <= Y of the sums of (A2.2), plus delta. The term delta carries the edge of
the t range below Y/4 and the bounded coefficients; the lower bound c qQ/Y keeps
delta of the printed size. -/
theorem gallagher_saffari_vaughan :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C c X0 : ℝ, 0 < C ∧ 0 < c ∧ ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
        ∀ χ : DirichletCharacter ℂ q,
          ∃ δ : ℝ, c * ((q : ℝ) * (H / Real.log X ^ B)) / windowY X ε ≤ δ ∧
            δ ≤ (q : ℝ) * (H / Real.log X ^ B) / windowY X ε ∧
            (∫ β in -((q : ℝ) * (H / Real.log X ^ B))⁻¹..((q : ℝ) * (H / Real.log X ^ B))⁻¹,
              ‖∑ m ∈ squareWindow (windowY X ε),
                (roughWeight (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) m * χ m -
                  (if χ = 1 then ((Task556a.f2Weight
                      (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ)
                   else 0)) * fourier ((m ^ 2 : ℕ) : ℤ) (β : AddCircle (1 : ℝ))‖ ^ 2) ≤
              C * (((q : ℝ) * (H / Real.log X ^ B)) ^ (-2 : ℤ) *
                (∫ t in windowY X ε / 4..windowY X ε,
                  ‖roughDefect χ (windowY X ε) (Real.log X ^ B) δ t‖ ^ 2) + δ) := by
  sorry

/-! ## Proved combinations -/

/-- PROVED from the LEAF gallagher_saffari_vaughan, CONDITIONAL ON A22Corr. P0088 page 6
before display 20: inserting (A2.2) into the Gallagher bound gives C P^(-4) for each
arc integral of |W2|^2, since (qQ)^(-2) (qQ)^2 = 1 and delta is at most qQ/Y, at most
H/Y, at most P^(-4) in the block range. No sorry of its own. -/
theorem arc_char_mean_square (h : A22Corr) :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
        ∀ χ : DirichletCharacter ℂ q,
          (∫ β in -((q : ℝ) * (H / Real.log X ^ B))⁻¹..((q : ℝ) * (H / Real.log X ^ B))⁻¹,
              ‖∑ m ∈ squareWindow (windowY X ε),
                (roughWeight (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) m * χ m -
                  (if χ = 1 then ((Task556a.f2Weight
                      (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ)
                   else 0)) * fourier ((m ^ 2 : ℕ) : ℤ) (β : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * (Real.log X ^ B) ^ (-4 : ℤ) := by
  intro B hB ε hε hε'
  obtain ⟨C, c, X0, hC, hc, kG⟩ := gallagher_saffari_vaughan B hB ε hε hε'
  obtain ⟨CA, XA, hCA, kA⟩ := h B hB ε hε hε'
  refine ⟨C * (CA + 1), max (max X0 XA) 3, by positivity, ?_⟩
  intro X H hX hlo hhi q hq hqP χ
  have hX0 : X0 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXA : XA ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX3 : (3 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hP : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL B
  have hY : 0 < windowY X ε := Real.rpow_pos_of_pos (by linarith) _
  have hH : 0 < H := lt_of_lt_of_le (by
    have : 0 < X ^ (7 / 18 + ε) := Real.rpow_pos_of_pos (by linarith) _
    positivity) hlo
  set P := Real.log X ^ B with hPdef
  set Y := windowY X ε with hYdef
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqQ : 0 < (q : ℝ) * (H / P) := by positivity
  obtain ⟨δ, hδ1, hδ2, hI⟩ := kG X H hX0 hlo hhi q hq hqP χ
  have hδ : 0 < δ := lt_of_lt_of_le (by positivity) hδ1
  have hA := kA X H hXA hlo hhi q hq hqP χ δ hδ hδ2
  have hP4 : 0 < P ^ (-4 : ℤ) := zpow_pos hP _
  have hδP : δ ≤ P ^ (-4 : ℤ) := by
    have h1 : (q : ℝ) * (H / P) ≤ H := by
      calc (q : ℝ) * (H / P) ≤ P * (H / P) :=
            mul_le_mul_of_nonneg_right hqP (by positivity)
        _ = H := by field_simp
    have h2 : H / Y ≤ P ^ (-4 : ℤ) := by
      rw [div_le_iff₀ hY]; linarith
    calc δ ≤ (q : ℝ) * (H / P) / Y := hδ2
      _ ≤ H / Y := div_le_div_of_nonneg_right h1 hY.le
      _ ≤ P ^ (-4 : ℤ) := h2
  have hz : 0 ≤ ((q : ℝ) * (H / P)) ^ (-2 : ℤ) := (zpow_pos hqQ _).le
  have hone : ((q : ℝ) * (H / P)) ^ (-2 : ℤ) * ((q : ℝ) * (H / P)) ^ 2 = 1 := by
    rw [zpow_neg, zpow_two, sq]
    field_simp
  calc _ ≤ C * (((q : ℝ) * (H / P)) ^ (-2 : ℤ) *
          (∫ t in Y / 4..Y, ‖roughDefect χ Y P δ t‖ ^ 2) + δ) := hI
    _ ≤ C * (((q : ℝ) * (H / P)) ^ (-2 : ℤ) *
          (CA * ((q : ℝ) * (H / P)) ^ 2 * P ^ (-4 : ℤ)) + P ^ (-4 : ℤ)) := by
        gcongr
    _ = C * (CA + 1) * P ^ (-4 : ℤ) := by
        rw [show ((q : ℝ) * (H / P)) ^ (-2 : ℤ) * (CA * ((q : ℝ) * (H / P)) ^ 2 * P ^ (-4 : ℤ))
            = CA * P ^ (-4 : ℤ) * (((q : ℝ) * (H / P)) ^ (-2 : ℤ) * ((q : ℝ) * (H / P)) ^ 2)
            by ring, hone]
        ring

/-- PROVED. The arcs of arcPairs P number at most 2 P^2 when P is at least one:
q runs over 1 to the floor of P and a over 0 to the floor of P. -/
theorem card_arcPairs_le {P : ℝ} (hP : 1 ≤ P) : ((arcPairs P).card : ℝ) ≤ 2 * P ^ 2 := by
  have hc : (arcPairs P).card ≤ ⌊P⌋₊ * (⌊P⌋₊ + 1) := by
    unfold arcPairs
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Finset.card_product, Nat.card_Icc, Finset.card_range, Nat.add_sub_cancel]
  have hf : (⌊P⌋₊ : ℝ) ≤ P := Nat.floor_le (by linarith)
  have hf0 : (0 : ℝ) ≤ ⌊P⌋₊ := Nat.cast_nonneg _
  calc ((arcPairs P).card : ℝ) ≤ ((⌊P⌋₊ * (⌊P⌋₊ + 1) : ℕ) : ℝ) := by exact_mod_cast hc
    _ = (⌊P⌋₊ : ℝ) * ((⌊P⌋₊ : ℝ) + 1) := by push_cast; ring
    _ ≤ P * (P + P) := by gcongr
    _ = 2 * P ^ 2 := by ring

/-- The exact statement of Prep1121DKLMajorCut.S2_sub_S2star_major_mean_square, P0088
page 5 displays 18, 19 and page 6 display 20, from the LEAF pieces arc_localization,
char_orthogonality_18 and gallagher_saffari_vaughan, CONDITIONAL ON A22Corr.
The coprimality (A2.1) for X large is Task556a.roughWeight_eventually_coprime, PROVED.
Each arc gives at most phi(q) C P^(-4), at most C P^(-3); at most 2 P^2 arcs give
2 C P^(-1), at most 2 C P^(-1/2). No sorry of its own. -/
theorem S2_sub_S2star_major_mean_square_of_pieces (h : A22Corr) :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        (∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs H (Real.log X ^ B),
          ‖roughSum (windowY X ε) (Real.log X ^ B) α -
            S2star (windowY X ε) H (Real.log X ^ B) α‖ ^ 2) ≤
            C * (Real.log X ^ B) ^ (-(1 / 2 : ℝ)) := by
  intro B hB ε hε hε'
  obtain ⟨C1, X1, hC1, k1⟩ := arc_char_mean_square h B hB ε hε hε'
  obtain ⟨X2, k2⟩ := arc_localization B hB ε hε hε'
  obtain ⟨X3, k3⟩ := Filter.eventually_atTop.mp (roughWeight_eventually_coprime B ε hε)
  refine ⟨2 * C1, max (max X1 X2) (max X3 3), by positivity, ?_⟩
  intro X H hX hlo hhi
  have hX1 : X1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX2 : X2 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX3 : X3 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX3' : (3 : ℝ) ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hP1 : 1 ≤ Real.log X ^ B := Real.one_le_rpow hL1 hB.le
  have hcopX := k3 X hX3
  set P := Real.log X ^ B with hPdef
  set Y := windowY X ε with hYdef
  have hP0 : 0 < P := by linarith
  have hP4 : 0 < P ^ (-4 : ℤ) := zpow_pos hP0 _
  have hH : 0 < H := lt_of_lt_of_le (by
    have : 0 < X ^ (7 / 18 + ε) := Real.rpow_pos_of_pos (by linarith) _
    positivity) hlo
  have harc : ∀ v ∈ arcPairs P,
      (∫ β in -((v.1 : ℝ) * (H / P))⁻¹..((v.1 : ℝ) * (H / P))⁻¹,
        ‖roughSum Y P ((v.2 : ℝ) / v.1 + β) -
          U1534.gaussS v.1 v.2 / (Nat.totient v.1 : ℂ) * T2 Y P β‖ ^ 2) ≤
        P * (C1 * P ^ (-4 : ℤ)) := by
    intro v hv
    obtain ⟨hvp, -, hcop⟩ := Finset.mem_filter.mp hv
    have hq := (Finset.mem_Icc.mp (Finset.mem_product.mp hvp).1)
    have hq1 : 1 ≤ v.1 := hq.1
    have hqP : (v.1 : ℝ) ≤ P := (Nat.cast_le.mpr hq.2).trans (Nat.floor_le hP0.le)
    have : NeZero v.1 := ⟨by omega⟩
    have hr : -((v.1 : ℝ) * (H / P))⁻¹ ≤ ((v.1 : ℝ) * (H / P))⁻¹ := by
      have : 0 ≤ ((v.1 : ℝ) * (H / P))⁻¹ := by positivity
      linarith
    have hW : ∀ χ : DirichletCharacter ℂ v.1, Continuous (fun β : ℝ =>
        ‖∑ m ∈ squareWindow Y,
          (roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m * χ m -
            (if χ = 1 then ((Task556a.f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ)
             else 0)) * fourier ((m ^ 2 : ℕ) : ℤ) (β : AddCircle (1 : ℝ))‖ ^ 2) := fun χ =>
      (Prep1121DKLMajorCut.trig_continuous _ _ (fun m => ((m ^ 2 : ℕ) : ℤ))).norm.pow 2
    have hT2 : Continuous (fun β : ℝ => T2 Y P β) := by
      unfold T2
      exact Prep1121DKLMajorCut.trig_continuous _ _ (fun m => ((m ^ 2 : ℕ) : ℤ))
    have hL : Continuous (fun β : ℝ => ‖roughSum Y P ((v.2 : ℝ) / v.1 + β) -
          U1534.gaussS v.1 v.2 / (Nat.totient v.1 : ℂ) * T2 Y P β‖ ^ 2) :=
      (((Prep1121DKLMajorCut.cont_S2 Y P).comp (continuous_const.add continuous_id)).sub
        (continuous_const.mul hT2)).norm.pow 2
    have hcard : (Finset.univ : Finset (DirichletCharacter ℂ v.1)).card = Nat.totient v.1 := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ v.1
    have htot : ((Nat.totient v.1 : ℕ) : ℝ) ≤ P :=
      (Nat.cast_le.mpr (Nat.totient_le v.1)).trans hqP
    calc _ ≤ ∫ β in -((v.1 : ℝ) * (H / P))⁻¹..((v.1 : ℝ) * (H / P))⁻¹,
          ∑ χ : DirichletCharacter ℂ v.1,
            ‖∑ m ∈ squareWindow Y,
              (roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m * χ m -
                (if χ = 1 then ((Task556a.f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ)
                 else 0)) * fourier ((m ^ 2 : ℕ) : ℤ) (β : AddCircle (1 : ℝ))‖ ^ 2 := by
          refine intervalIntegral.integral_mono_on hr (hL.intervalIntegrable _ _)
            ((continuous_finsetSum _ fun χ _ => hW χ).intervalIntegrable _ _) ?_
          intro β _
          exact char_orthogonality_18 Y P v.1 v.2 hq1 hcop
            (fun m hm => hcopX v.1 (by omega) hqP m hm) β
      _ = ∑ χ : DirichletCharacter ℂ v.1, ∫ β in -((v.1 : ℝ) * (H / P))⁻¹..((v.1 : ℝ) * (H / P))⁻¹,
            ‖∑ m ∈ squareWindow Y,
              (roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m * χ m -
                (if χ = 1 then ((Task556a.f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ)
                 else 0)) * fourier ((m ^ 2 : ℕ) : ℤ) (β : AddCircle (1 : ℝ))‖ ^ 2 :=
          intervalIntegral.integral_finsetSum fun χ _ => (hW χ).intervalIntegrable _ _
      _ ≤ ∑ _χ : DirichletCharacter ℂ v.1, C1 * P ^ (-4 : ℤ) :=
          Finset.sum_le_sum fun χ _ => k1 X H hX1 hlo hhi v.1 hq1 hqP χ
      _ = (Nat.totient v.1 : ℝ) * (C1 * P ^ (-4 : ℤ)) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
      _ ≤ P * (C1 * P ^ (-4 : ℤ)) := by gcongr
  have hcardA := card_arcPairs_le hP1
  calc _ ≤ _ := k2 X H hX2 hlo hhi
    _ ≤ ∑ _v ∈ arcPairs P, P * (C1 * P ^ (-4 : ℤ)) := Finset.sum_le_sum harc
    _ = ((arcPairs P).card : ℝ) * (P * (C1 * P ^ (-4 : ℤ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * P ^ 2) * (P * (C1 * P ^ (-4 : ℤ))) := by gcongr
    _ = 2 * C1 * P ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one, zpow_neg]
        field_simp
    _ ≤ 2 * C1 * P ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num))
          (by positivity)

example : type_of% @Prep1121DKLMajorCut.S2_sub_S2star_major_mean_square :=
  S2_sub_S2star_major_mean_square_of_pieces

end LeanLab.KumchevLiu2007.Prep1122KLGallagherCut

#print axioms LeanLab.KumchevLiu2007.Prep1122KLGallagherCut.char_orthogonality_18
#print axioms LeanLab.KumchevLiu2007.Prep1122KLGallagherCut.arc_localization
#print axioms LeanLab.KumchevLiu2007.Prep1122KLGallagherCut.gallagher_saffari_vaughan
#print axioms LeanLab.KumchevLiu2007.Prep1122KLGallagherCut.arc_char_mean_square
#print axioms LeanLab.KumchevLiu2007.Prep1122KLGallagherCut.card_arcPairs_le
#print axioms LeanLab.KumchevLiu2007.Prep1122KLGallagherCut.S2_sub_S2star_major_mean_square_of_pieces
