/-
P0054 J. Pintz, An approximate formula for Goldbach's problem with applications,
Riv. Mat. Univ. Parma 12 (2021) 181-199. Read from the author's copy,
http://real.mtak.hu/124681/1/Cikk2020Rivista.pdf, the journal PDF has no text layer.

What is stated here, side by side in STATEMENTS.md:
* Theorem 3, E(X) ≤ C(ε) X^{0.72+ε}, PROVED from Theorem 3', which is the lab's cited
  `ExceptionalSet.pintz`, EventuallyBelow 0.72. Theorem 3' is Pintz 2018, P0016.
* Theorem 4, Pintz-Ruzsa K = 8, is the lab's cited `Linnik.pintzRuzsa2`; restated here as a
  pointer, no new sorry.
* (5.3) E_k(N), the n ≤ N with 2n^k not a sum of two primes, defined as `EPoly`.
* Theorem 5, Perelli-Pintz, E_2(N) ≪_ε N^{4/5+ε}, CITED with sorry, proof only sketched in
  the paper, full proof in unpublished joint work.
* (5.4) Perelli, E_k(N) ≪_A N (log N)^{-A}, and the shape of (5.5), a power saving, PROVED at
  k = 2 from Theorem 5.
* New small links, PROVED: E_1(N) ≤ E(2N) + 1, so any E(X) ≪ X^θ bound transfers to E_1;
  binary Goldbach forces E_k(N) ≤ 1 for k ≥ 1; the term n = 1 is always counted, since 2 is
  not a sum of two primes, so E_k(N) ≥ 1 for N ≥ 1, harmless for every bound in the paper.
Not stated: Theorems 1 and 2 and Lemma 2, sums over generalized exceptional zeros with
notation the paper takes from Pin1 and Pin2; recorded in STATEMENTS.md.

AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach itself is OPEN.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.ExceptionalSet.Statements

namespace LeanLab.ExceptionalSet.Pintz2021
open Real Filter Topology LeanLab.ExceptionalSet

attribute [local instance] Classical.propDecidable

/-! ### Theorem 3 from Theorem 3' -/

/-- Theorem 3 of the paper: for every ε > 0, E(X) ≤ C(ε) X^{0.72+ε}. -/
def Theorem3 : Prop := ∀ ε : ℝ, 0 < ε → PowerBound (0.72 + ε)

/-- Theorem 3' is `EventuallyBelow 0.72`, the lab's cited `pintz`. Theorem 3 follows. -/
theorem theorem3_of_theorem3' (h : EventuallyBelow 0.72) : Theorem3 := by
  intro ε hε
  exact powerBound_mono (by linarith) (powerBound_of_eventuallyBelow (by norm_num) h)

/-! ### E_k(N), display (5.3) -/

/-- `EPoly k N`, the number of `n` with `1 ≤ n ≤ N` such that `2 n^k` is not a sum of two
primes, display (5.3). -/
noncomputable def EPoly (k N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => ¬ IsGoldbachSum (2 * n ^ k))).card

theorem EPoly_le (k N : ℕ) : EPoly k N ≤ N := by
  unfold EPoly
  refine (Finset.card_filter_le _ _).trans ?_
  simp

theorem not_goldbach_two : ¬ IsGoldbachSum 2 := by
  rintro ⟨p, q, hp, hq, h⟩
  have := hp.two_le; have := hq.two_le; omega

/-- The term `n = 1` is always an exception: `2 · 1^k = 2`. -/
theorem one_le_EPoly (k : ℕ) {N : ℕ} (hN : 1 ≤ N) : 1 ≤ EPoly k N := by
  unfold EPoly
  apply Finset.card_pos.mpr
  exact ⟨1, by simp [Finset.mem_Icc, hN, not_goldbach_two]⟩

/-- Binary Goldbach leaves only the trivial exception `n = 1`. -/
theorem EPoly_le_one_of_binaryGoldbach (h : BinaryGoldbach) {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    EPoly k N ≤ 1 := by
  unfold EPoly
  have hsub : (Finset.Icc 1 N).filter (fun n => ¬ IsGoldbachSum (2 * n ^ k)) ⊆ {1} := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    simp only [Finset.mem_singleton]
    by_contra hne
    have hn2 : 2 ≤ n := by omega
    have hpow : 2 ≤ n ^ k := by
      calc 2 ≤ n := hn2
        _ = n ^ 1 := (pow_one n).symm
        _ ≤ n ^ k := Nat.pow_le_pow_right (by omega) hk
    exact hn.2 (h _ (even_two_mul _) (by omega))
  exact (Finset.card_le_card hsub).trans (by simp)

/-- `E_1(N) ≤ E(2N) + 1`: an exception `n ≥ 2` gives the even exception `2n ≤ 2N`. -/
theorem EPoly_one_le (N : ℕ) : EPoly 1 N ≤ E (2 * N) + 1 := by
  unfold EPoly E
  set S := (Finset.Icc 1 N).filter (fun n => ¬ IsGoldbachSum (2 * n ^ 1))
  set T := (Finset.Icc 4 (2 * N)).filter (fun n => Even n ∧ ¬ IsGoldbachSum n)
  have hsub : S ⊆ insert 1 (T.image (fun m : ℕ => m / 2)) := by
    intro n hn
    simp only [S, Finset.mem_filter, Finset.mem_Icc, pow_one] at hn
    rcases Nat.eq_or_lt_of_le hn.1.1 with h1 | h1
    · exact Finset.mem_insert.mpr (Or.inl h1.symm)
    · refine Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨2 * n, ?_, by omega⟩))
      simp only [T, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, even_two_mul _, hn.2⟩
  calc S.card ≤ (insert 1 (T.image (fun m : ℕ => m / 2))).card := Finset.card_le_card hsub
    _ ≤ (T.image (fun m : ℕ => m / 2)).card + 1 := Finset.card_insert_le _ _
    _ ≤ T.card + 1 := Nat.add_le_add_right (Finset.card_image_le (f := fun m : ℕ => m / 2)) 1

/-! ### Bounds for E_k -/

/-- `E_k(N) ≪ N^θ`. -/
def PolyPowerBound (k : ℕ) (θ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → (EPoly k N : ℝ) ≤ C * (N : ℝ) ^ θ

/-- `E_k(N) ≪_A N (log N)^{-A}` for every `A > 0`, Perelli's (5.4). -/
def PolyLogPowerSaving (k : ℕ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → (EPoly k N : ℝ) ≤ C * N / Real.log N ^ A

/-- The shape of (5.5) and (5.6): `E_k(N) ≪ N^{1-δ}` for some `δ > 0`. -/
def PolyPowerSaving (k : ℕ) : Prop := ∃ δ : ℝ, 0 < δ ∧ PolyPowerBound k (1 - δ)

/-- Theorem 5, Perelli-Pintz, display (5.8): `E_2(N) ≪_ε N^{4/5+ε}` for every `ε > 0`. -/
def Theorem5 : Prop := ∀ ε : ℝ, 0 < ε → PolyPowerBound 2 (4 / 5 + ε)

/-- CITED. Theorem 5 of the paper; only a sketch is given, the full proof is announced as
joint work of Perelli and Pintz. -/
theorem perelliPintz : Theorem5 := by sorry

theorem polyPowerBound_mono {k : ℕ} {θ θ' : ℝ} (hθ : θ ≤ θ') (h : PolyPowerBound k θ) :
    PolyPowerBound k θ' := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc (EPoly k N : ℝ) ≤ C * (N : ℝ) ^ θ := hC N hN
    _ ≤ max C 0 * (N : ℝ) ^ θ := by gcongr; exact le_max_left _ _
    _ ≤ max C 0 * (N : ℝ) ^ θ' :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 hθ) (le_max_right _ _)

theorem polyLogPowerSaving_of_polyPowerBound {k : ℕ} {θ : ℝ} (hθ : θ < 1)
    (h : PolyPowerBound k θ) : PolyLogPowerSaving k := by
  obtain ⟨C, hC⟩ := h
  intro A hA
  set ε : ℝ := (1 - θ) / A with hε
  have hεpos : 0 < ε := div_pos (by linarith) hA
  refine ⟨max C 0 * (1 / ε ^ A), fun X hX => ?_⟩
  have hX1 : (1 : ℕ) ≤ X := by omega
  have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hlogpos A
  have hlog : Real.log X ≤ (X : ℝ) ^ ε / ε := Real.log_le_rpow_div hXpos.le hεpos
  have hkey : Real.log X ^ A ≤ (X : ℝ) ^ (1 - θ) / ε ^ A := by
    calc Real.log X ^ A ≤ ((X : ℝ) ^ ε / ε) ^ A :=
          Real.rpow_le_rpow hlogpos.le hlog hA.le
      _ = (X : ℝ) ^ (1 - θ) / ε ^ A := by
          rw [Real.div_rpow (Real.rpow_nonneg hXpos.le _) hεpos.le, ← Real.rpow_mul hXpos.le]
          congr 2
          rw [hε]; field_simp
  have hC0 : (EPoly k X : ℝ) ≤ max C 0 * (X : ℝ) ^ θ :=
    (hC X hX1).trans (by gcongr; exact le_max_left _ _)
  rw [le_div_iff₀ hlogA]
  have hM : 0 ≤ max C 0 := le_max_right _ _
  calc (EPoly k X : ℝ) * Real.log X ^ A
        ≤ max C 0 * (X : ℝ) ^ θ * ((X : ℝ) ^ (1 - θ) / ε ^ A) := by
        apply mul_le_mul hC0 hkey hlogA.le (by positivity)
    _ = max C 0 * (1 / ε ^ A) * ((X : ℝ) ^ θ * (X : ℝ) ^ (1 - θ)) := by ring
    _ = max C 0 * (1 / ε ^ A) * X := by
        rw [← Real.rpow_add hXpos]; norm_num

/-- Theorem 5 gives a power saving for `E_2`, the shape of (5.5) at `k = 2`, with any
`δ < 1/5`; here `δ = 1/10`. -/
theorem polyPowerSaving_two_of_theorem5 (h : Theorem5) : PolyPowerSaving 2 :=
  ⟨1 / 10, by norm_num, polyPowerBound_mono (by norm_num) (h (1 / 10) (by norm_num))⟩

/-- Theorem 5 implies Perelli's (5.4) at `k = 2`. -/
theorem perelli_two_of_theorem5 (h : Theorem5) : PolyLogPowerSaving 2 :=
  polyLogPowerSaving_of_polyPowerBound (θ := 4 / 5 + 1 / 10) (by norm_num)
    (h (1 / 10) (by norm_num))

/-- Any `E(X) ≪ X^θ` with `0 ≤ θ ≤ 1` gives `E_1(N) ≪ N^θ`, through `E_1(N) ≤ E(2N) + 1`. -/
theorem polyPowerBound_one_of_powerBound {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (h : PowerBound θ) : PolyPowerBound 1 θ := by
  obtain ⟨C, hC⟩ := h
  refine ⟨2 * max C 0 + 1, fun N hN => ?_⟩
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have h2N : 1 ≤ 2 * N := by omega
  have hE := hC (2 * N) h2N
  have hpowN : (1 : ℝ) ≤ (N : ℝ) ^ θ := Real.one_le_rpow hNr h0
  have h2 : (2 : ℝ) ^ θ ≤ 2 := by
    calc (2 : ℝ) ^ θ ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      _ = 2 := Real.rpow_one 2
  have hsplit : ((2 * N : ℕ) : ℝ) ^ θ = (2 : ℝ) ^ θ * (N : ℝ) ^ θ := by
    push_cast; exact Real.mul_rpow (by norm_num) hNpos.le
  have hM : 0 ≤ max C 0 := le_max_right _ _
  have hEle : (E (2 * N) : ℝ) ≤ 2 * max C 0 * (N : ℝ) ^ θ := by
    calc (E (2 * N) : ℝ) ≤ C * ((2 * N : ℕ) : ℝ) ^ θ := hE
      _ ≤ max C 0 * ((2 * N : ℕ) : ℝ) ^ θ := by gcongr; exact le_max_left _ _
      _ = max C 0 * ((2 : ℝ) ^ θ * (N : ℝ) ^ θ) := by rw [hsplit]
      _ ≤ max C 0 * (2 * (N : ℝ) ^ θ) := by gcongr
      _ = 2 * max C 0 * (N : ℝ) ^ θ := by ring
  have hP : (EPoly 1 N : ℝ) ≤ E (2 * N) + 1 := by exact_mod_cast EPoly_one_le N
  calc (EPoly 1 N : ℝ) ≤ E (2 * N) + 1 := hP
    _ ≤ 2 * max C 0 * (N : ℝ) ^ θ + (N : ℝ) ^ θ := by linarith
    _ = (2 * max C 0 + 1) * (N : ℝ) ^ θ := by ring

/-- Zhao's `E(X) ≪ X^{7/10}`, P0040, gives `E_1(N) ≪ N^{7/10}`. -/
theorem polyOne_of_zhao (h : PowerBound (7 / 10)) : PolyPowerBound 1 (7 / 10) :=
  polyPowerBound_one_of_powerBound (by norm_num) (by norm_num) h

/-! ### Explicit ranges from Goldbach verifications, unit U-0276 -/

/-- A verification of even Goldbach up to `M` leaves only `n = 1` below `(M/2)^{1/k}`. -/
theorem EPoly_le_one_of_upTo {M : ℕ} (h : EvenGoldbachUpTo M) {k : ℕ} (hk : 1 ≤ k) {N : ℕ}
    (hN : 2 * N ^ k ≤ M) : EPoly k N ≤ 1 := by
  unfold EPoly
  have hsub : (Finset.Icc 1 N).filter (fun n => ¬ IsGoldbachSum (2 * n ^ k)) ⊆ {1} := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    simp only [Finset.mem_singleton]
    by_contra hne
    have hn2 : 2 ≤ n := by omega
    have hpow : 2 ≤ n ^ k := by
      calc 2 ≤ n := hn2
        _ = n ^ 1 := (pow_one n).symm
        _ ≤ n ^ k := Nat.pow_le_pow_right (by omega) hk
    have hle : 2 * n ^ k ≤ M :=
      le_trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hn.1.2 k)) hN
    exact hn.2 (h _ (even_two_mul _) (by omega) hle)
  exact (Finset.card_le_card hsub).trans (by simp)

theorem EPoly_eq_one_of_upTo {M : ℕ} (h : EvenGoldbachUpTo M) {k : ℕ} (hk : 1 ≤ k) {N : ℕ}
    (h1 : 1 ≤ N) (hN : 2 * N ^ k ≤ M) : EPoly k N = 1 :=
  le_antisymm (EPoly_le_one_of_upTo h hk hN) (one_le_EPoly k h1)

/-- From the Oliveira e Silva, Herzog and Pardi verification to `4 · 10^18`, cited in the lab as
`Verifications.oesilva_even`: `E_2(N) = 1`, only `n = 1`, for `1 ≤ N ≤ 1414213562`. -/
theorem EPoly_two_eq_one_of_oesilva (h : EvenGoldbachUpTo (4 * 10 ^ 18)) {N : ℕ} (h1 : 1 ≤ N)
    (hN : N ≤ 1414213562) : EPoly 2 N = 1 :=
  EPoly_eq_one_of_upTo h (by norm_num) h1
    (le_trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hN 2)) (by norm_num))

/-- The same for `E_1`: only `n = 1` for `1 ≤ N ≤ 2 · 10^18`. -/
theorem EPoly_one_eq_one_of_oesilva (h : EvenGoldbachUpTo (4 * 10 ^ 18)) {N : ℕ} (h1 : 1 ≤ N)
    (hN : N ≤ 2 * 10 ^ 18) : EPoly 1 N = 1 :=
  EPoly_eq_one_of_upTo h le_rfl h1 (by rw [pow_one]; omega)

/-- 1414213562 is the largest `N` the `4 · 10^18` verification covers at `k = 2`. -/
theorem oesilva_two_sharp : 2 * 1414213562 ^ 2 ≤ 4 * 10 ^ 18 ∧ 4 * 10 ^ 18 < 2 * 1414213563 ^ 2 := by
  norm_num

end LeanLab.ExceptionalSet.Pintz2021
