/-
P0069 Baker Harman Pintz 1997, pages 11, 48, 50 and 53, read from papers/P0069-original.pdf.
Burst burst-20261122, session S130, unit upD_kept_52-p3 on the LEAF kept52_box_reduce of
Prep1122KeptWellspacedSplit52.lean.

Page 53 keeps the terms of k_m to which Lemma 33 applies. The reduction of the kept polynomial on
one block to Lemma 33 has two parts: the cutting of p1, p2, p3 and n4 into boxes, as in the proof
of Lemma 34 on page 50, which is the one LEAF s130_box_decomp, HARD; and the bookkeeping,
PROVED here: Cauchy Schwarz over at most L^D boxes, Lemma 33 on each inner box with A + 2D in
place of A, and Lemma 1, display 3.3 on page 11, on the boundary polynomial after the shift to
the block centre, where qT + Y is at most 3Y since Q is at most Y.
s130_box_reduce_split has the exact statement of kept52_box_reduce and is PROVED from the LEAF.

New file, no new definition, no existing statement changed. AI wrote the Lean code.
Goldbach is open.
-/
import LeanLab.BHP1997.UpperShortC165Leaves

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open MeasureTheory

/-- LEAF: P0069 page 53, the kept terms of k_m cut into boxes, as in the proof of Lemma 34 on
page 50: on one block of length at most T2 inside T0 <= |t| <= Y the kept polynomial is a sum of
at most L^D products LMN with (beta1, beta2) in upperPairRegion, (3.1) for all factors and (3.2)
for M and N on S by Lemma 5, plus a boundary polynomial of length Y at the block centre with
G at most C L^(-A-1). B, c1, c2, K come first, D depends on A. Hypotheses: the statements of
kept52_prime_32 and kept52_mvt_lemma1. HARD. -/
theorem s130_box_decomp {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8)
    (H5 : ∀ A' : ℝ, 0 < A' → ∃ K C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ P u v : ℝ, (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ P → P ≤ x ^ (11 / 20 + ε) →
        P ≤ u → u ≤ v → v ≤ 2 * P →
      ∀ t : ℝ, Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ |t| → |t| ≤ x ^ (11 / 20 + ε) →
        ‖∑ p ∈ (Finset.range (⌊v⌋₊ + 1)).filter
              (fun n : ℕ => n.Prime ∧ u < (n : ℝ) ∧ (n : ℝ) ≤ v),
            (1 : DirichletCharacter ℂ q) (p : ZMod q) / (p : ℂ) ^ Thm4.half t‖ ≤
          K * P ^ (1 / 2 : ℝ) * Real.log x ^ (-A'))
    (H1 : ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∃ C : ℝ, ∀ x T F : ℝ, ∀ q : ℕ,
      2 ≤ x → 1 ≤ q → (q : ℝ) ≤ x → 2 ≤ T → T ≤ x → 1 ≤ F → F ≤ x →
      ∀ S : Finset ℝ, (∀ t ∈ S, |t| ≤ T) → (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
      ∀ a : ℕ → ℂ,
        ∑ t ∈ S, ‖Thm4.dirPoly a c₁ c₂ F (1 : DirichletCharacter ℂ q) (Thm4.half t)‖ ^ 2 ≤
          C * Real.log x * ((q : ℝ) * T + F) *
            ∑ n ∈ (Finset.range (⌊c₂ * F⌋₊ + 1)).filter
                (fun n : ℕ => c₁ * F < n ∧ (n : ℝ) < c₂ * F), ‖a n‖ ^ 2 / n) :
    ∃ B c₁ c₂ : ℝ, ∃ K : ℝ → ℝ, 0 < c₁ ∧ c₁ < c₂ ∧
    ∀ A : ℝ, 0 < A → ∃ D : ℝ, 0 ≤ D ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q →
      q ≤ sieveQ ε x →
      ∀ a b : ℝ, a ≤ b → b - a ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) →
      ((Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ a ∧ b ≤ x ^ (11 / 20 + ε)) ∨
        (-x ^ (11 / 20 + ε) ≤ a ∧ b ≤ -Real.exp (Real.log x ^ (1 / 3 : ℝ)))) →
      ∀ S : Finset ℝ, (∀ t ∈ S, a ≤ t ∧ t ≤ b) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
      ∃ k : ℕ, (k : ℝ) ≤ Real.log x ^ D ∧
      ∃ (β₁ β₂ : ℕ → ℝ) (eL eM eN : ℕ → ℕ → ℂ) (r : ℕ → ℂ),
        (∀ i < k, upperPairRegion ε (β₁ i) (β₂ i) ∧ Thm4.CoeffBound (eL i) B ∧
          Thm4.CoeffBound (eM i) B ∧ Thm4.CoeffBound (eN i) B ∧
          (∀ A' : ℝ, 0 < A' → ∀ t ∈ S,
            ‖Thm4.dirPoly (eM i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁ i) (1 : DirichletCharacter ℂ q)
                (Thm4.half t)‖ ≤
              K A' * ((x ^ (11 / 20 + ε)) ^ β₁ i) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) ∧
          (∀ A' : ℝ, 0 < A' → ∀ t ∈ S,
            ‖Thm4.dirPoly (eN i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂ i) (1 : DirichletCharacter ℂ q)
                (Thm4.half t)‖ ≤
              K A' * ((x ^ (11 / 20 + ε)) ^ β₂ i) ^ (1 / 2 : ℝ) * Real.log x ^ (-A'))) ∧
        ∑ n ∈ (Finset.range (⌊c₂ * (x ^ (11 / 20 + ε))⌋₊ + 1)).filter
            (fun n : ℕ => c₁ * (x ^ (11 / 20 + ε)) < n ∧ (n : ℝ) < c₂ * (x ^ (11 / 20 + ε))), ‖r n‖ ^ 2 / n ≤
          C * Real.log x ^ (-A - 1) ∧
        ∀ t ∈ S,
          ∑ m ∈ rightInterval ε x, (upperKept ε (x ^ (11 / 20 + ε)) m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) =
            ∑ i ∈ Finset.range k,
              Thm4.dirPoly (eL i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ i - β₂ i))
                  (1 : DirichletCharacter ℂ q) (Thm4.half t) *
                Thm4.dirPoly (eM i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t) *
                Thm4.dirPoly (eN i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t) +
              Thm4.dirPoly r c₁ c₂ (x ^ (11 / 20 + ε)) (1 : DirichletCharacter ℂ q)
                (Thm4.half (t - (a + b) / 2)) := by
  sorry

/-- P0069 page 53: the exact statement of the LEAF kept52_box_reduce, PROVED from the LEAF
s130_box_decomp, H33 and H1. -/
theorem s130_box_reduce_split {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8)
    (H33 : ∀ B c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
      ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ a b : ℝ, a ≤ b → b - a ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) →
      ∀ S : Finset ℝ, (∀ t ∈ S, a ≤ t ∧ t ≤ b) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
      ∀ β₁ β₂ : ℝ, upperPairRegion ε β₁ β₂ →
      ∀ eL eM eN : ℕ → ℂ, Thm4.CoeffBound eL B → Thm4.CoeffBound eM B →
        Thm4.CoeffBound eN B →
        (∀ A' : ℝ, 0 < A' → ∀ t ∈ S,
          ‖Thm4.dirPoly eM c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ≤
            K A' * ((x ^ (11 / 20 + ε)) ^ β₁) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
        (∀ A' : ℝ, 0 < A' → ∀ t ∈ S,
          ‖Thm4.dirPoly eN c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ≤
            K A' * ((x ^ (11 / 20 + ε)) ^ β₂) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
        ∑ t ∈ S, ‖Thm4.dirPoly eL c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ - β₂))
              (1 : DirichletCharacter ℂ q) (Thm4.half t) *
            Thm4.dirPoly eM c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁) (1 : DirichletCharacter ℂ q)
              (Thm4.half t) *
            Thm4.dirPoly eN c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ^ 2 ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    (H5 : ∀ A' : ℝ, 0 < A' → ∃ K C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ P u v : ℝ, (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ P → P ≤ x ^ (11 / 20 + ε) →
        P ≤ u → u ≤ v → v ≤ 2 * P →
      ∀ t : ℝ, Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ |t| → |t| ≤ x ^ (11 / 20 + ε) →
        ‖∑ p ∈ (Finset.range (⌊v⌋₊ + 1)).filter
              (fun n : ℕ => n.Prime ∧ u < (n : ℝ) ∧ (n : ℝ) ≤ v),
            (1 : DirichletCharacter ℂ q) (p : ZMod q) / (p : ℂ) ^ Thm4.half t‖ ≤
          K * P ^ (1 / 2 : ℝ) * Real.log x ^ (-A'))
    (H1 : ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∃ C : ℝ, ∀ x T F : ℝ, ∀ q : ℕ,
      2 ≤ x → 1 ≤ q → (q : ℝ) ≤ x → 2 ≤ T → T ≤ x → 1 ≤ F → F ≤ x →
      ∀ S : Finset ℝ, (∀ t ∈ S, |t| ≤ T) → (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
      ∀ a : ℕ → ℂ,
        ∑ t ∈ S, ‖Thm4.dirPoly a c₁ c₂ F (1 : DirichletCharacter ℂ q) (Thm4.half t)‖ ^ 2 ≤
          C * Real.log x * ((q : ℝ) * T + F) *
            ∑ n ∈ (Finset.range (⌊c₂ * F⌋₊ + 1)).filter
                (fun n : ℕ => c₁ * F < n ∧ (n : ℝ) < c₂ * F), ‖a n‖ ^ 2 / n) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ a b : ℝ, a ≤ b → b - a ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) →
      ((Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ a ∧ b ≤ x ^ (11 / 20 + ε)) ∨
        (-x ^ (11 / 20 + ε) ≤ a ∧ b ≤ -Real.exp (Real.log x ^ (1 / 3 : ℝ)))) →
      ∀ S : Finset ℝ, (∀ t ∈ S, a ≤ t ∧ t ≤ b) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
        ∑ t ∈ S, ‖∑ m ∈ rightInterval ε x, (upperKept ε (x ^ (11 / 20 + ε)) m : ℂ) *
            (1 : DirichletCharacter ℂ q) (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨B, c₁, c₂, K, hc₁, hc₁₂, hdec⟩ := s130_box_decomp hε hε8 H5 H1
  obtain ⟨C1, hH1⟩ := H1 c₁ c₂ hc₁ hc₁₂
  obtain ⟨D, hD0, Cd, hd⟩ := hdec A hA
  obtain ⟨C33, h33⟩ := H33 B c₁ c₂ hc₁ hc₁₂ K (A + 2 * D) (by linarith)
  refine ⟨max (max (max Cd C33) 2) (2 * |C33| + 6 * |C1| * |Cd|), ?_⟩
  intro x hx q hq1 hqQ a b hab hba hrange S hS hsp
  have hx2 : (2 : ℝ) ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxd : Cd ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_left _ _)) hx
  have hx33 : C33 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_left _ _)) hx
  have hCfin : 2 * |C33| + 6 * |C1| * |Cd| ≤
      max (max (max Cd C33) 2) (2 * |C33| + 6 * |C1| * |Cd|) := le_max_right _ _
  obtain ⟨k, hk, β₁, β₂, eL, eM, eN, r, hbox, hG, hid⟩ :=
    hd x hxd q hq1 hqQ a b hab hba hrange S hS hsp
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hε1 : (11 / 20 : ℝ) + ε ≤ 1 := by
    have : (1 : ℝ) / 10 ^ 8 ≤ 9 / 20 := by norm_num
    linarith
  have hY1 : 1 ≤ x ^ (11 / 20 + ε) := Real.one_le_rpow hx1 (by linarith)
  have hY0 : 0 ≤ x ^ (11 / 20 + ε) := by linarith
  have hYx : x ^ (11 / 20 + ε) ≤ x := by
    have := Real.rpow_le_rpow_of_exponent_le hx1 hε1
    rwa [Real.rpow_one] at this
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hQ1 : 1 ≤ sieveQ ε x := le_trans hq1 hqQ
  have hQY : (sieveQ ε x : ℝ) ≤ x ^ (11 / 20 + ε) := by
    unfold sieveQ
    have h2 : 1 ≤ (x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5)) :=
      Real.one_le_rpow hY1 (by norm_num)
    have h1 : (x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5)) ≤ x ^ (11 / 20 + ε) := by
      have := Real.rpow_le_rpow_of_exponent_le hY1
        (show (2 : ℝ) * (1 / 16 - 1 / 10 ^ 5) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    have h3 : ((x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5))) ^ (1 / 2 : ℝ) ≤
        (x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5)) := by
      have := Real.rpow_le_rpow_of_exponent_le h2 (show (1 / 2 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    have h4 : 0 ≤ ((x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5))) ^ (1 / 2 : ℝ) / 2 := by
      positivity
    have h5 := Nat.floor_le h4
    have h6 : 0 ≤ ((x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5))) ^ (1 / 2 : ℝ) := by positivity
    linarith
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hqQr : (q : ℝ) ≤ sieveQ ε x := by exact_mod_cast hqQ
  have hQpos : (1 : ℝ) ≤ sieveQ ε x := by exact_mod_cast hQ1
  have hqb : (q : ℝ) * (b - a) ≤ x ^ (11 / 20 + ε) := by
    have h1 : (q : ℝ) * (b - a) ≤ q * (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) :=
      mul_le_mul_of_nonneg_left hba hqpos.le
    have e : (q : ℝ) * (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) = x ^ (11 / 20 + ε) / sieveQ ε x := by
      rw [mul_div_assoc', mul_div_mul_left _ _ hqpos.ne']
    have h2 : x ^ (11 / 20 + ε) / sieveQ ε x ≤ x ^ (11 / 20 + ε) := div_le_self hY0 hQpos
    linarith
  have hba1 : b - a ≤ x ^ (11 / 20 + ε) := by
    have hq1r : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have : b - a ≤ (q : ℝ) * (b - a) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hq1r) (sub_nonneg.mpr hab)]
    linarith
  have hqx : (q : ℝ) ≤ x := by linarith
  have hT2 : (2 : ℝ) ≤ max 2 ((b - a) / 2) := le_max_left _ _
  have hTx : max 2 ((b - a) / 2) ≤ x := max_le hx2 (by linarith)
  have hqT : (q : ℝ) * max 2 ((b - a) / 2) ≤ 2 * x ^ (11 / 20 + ε) := by
    rcases le_total 2 ((b - a) / 2) with h | h
    · rw [max_eq_right h]
      have : (q : ℝ) * ((b - a) / 2) = (q * (b - a)) / 2 := by ring
      linarith
    · rw [max_eq_left h]
      linarith
  -- the boundary polynomial, by Lemma 1 after the shift to the block centre
  have hS'T : ∀ t ∈ S.image (fun t => t - (a + b) / 2), |t| ≤ max 2 ((b - a) / 2) := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨h1, h2⟩ := hS s hs
    have : (b - a) / 2 ≤ max 2 ((b - a) / 2) := le_max_right _ _
    rw [abs_le]; constructor <;> linarith
  have hsp' : ∀ t ∈ S.image (fun t => t - (a + b) / 2),
      ∀ t' ∈ S.image (fun t => t - (a + b) / 2), t ≠ t' → 1 ≤ |t - t'| := by
    intro t ht t' ht' hne
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp ht'
    have hne' : s ≠ s' := fun h => hne (by rw [h])
    have := hsp s hs s' hs' hne'
    rwa [sub_sub_sub_cancel_right]
  have hR := hH1 x (max 2 ((b - a) / 2)) (x ^ (11 / 20 + ε)) q hx2 hq1 hqx hT2 hTx hY1 hYx
    (S.image (fun t => t - (a + b) / 2)) hS'T hsp' r
  have hRsum : ∑ t ∈ S, ‖(Thm4.dirPoly r c₁ c₂ (x ^ (11 / 20 + ε)) (1 : DirichletCharacter ℂ q) (Thm4.half (t - (a + b) / 2)))‖ ^ 2 =
      ∑ t ∈ S.image (fun t => t - (a + b) / 2), ‖(Thm4.dirPoly r c₁ c₂ (x ^ (11 / 20 + ε)) (1 : DirichletCharacter ℂ q) (Thm4.half t))‖ ^ 2 := by
    rw [Finset.sum_image]
    intro u _ v _ h
    simpa using h
  have hG0 : 0 ≤ ∑ n ∈ (Finset.range (⌊c₂ * (x ^ (11 / 20 + ε))⌋₊ + 1)).filter
      (fun n : ℕ => c₁ * (x ^ (11 / 20 + ε)) < n ∧ (n : ℝ) < c₂ * (x ^ (11 / 20 + ε))), ‖r n‖ ^ 2 / n :=
    Finset.sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hpow1 : Real.log x * Real.log x ^ (-A - 1) = Real.log x ^ (-A) := by
    have := Real.rpow_add hL0 1 (-A - 1)
    rw [Real.rpow_one] at this
    rw [← this]; congr 1; ring
  have hRb : ∑ t ∈ S, ‖(Thm4.dirPoly r c₁ c₂ (x ^ (11 / 20 + ε)) (1 : DirichletCharacter ℂ q) (Thm4.half (t - (a + b) / 2)))‖ ^ 2 ≤
      3 * |C1| * |Cd| * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
    rw [hRsum]
    refine le_trans hR ?_
    have hLr : 0 ≤ Real.log x ^ (-A - 1) := Real.rpow_nonneg hL0.le _
    have hqT0 : 0 ≤ (q : ℝ) * max 2 ((b - a) / 2) + x ^ (11 / 20 + ε) := by positivity
    calc C1 * Real.log x * ((q : ℝ) * max 2 ((b - a) / 2) + x ^ (11 / 20 + ε)) * _
        ≤ |C1| * Real.log x * (3 * x ^ (11 / 20 + ε)) * (|Cd| * Real.log x ^ (-A - 1)) := by
          have hG' : _ ≤ |Cd| * Real.log x ^ (-A - 1) :=
            le_trans hG (mul_le_mul_of_nonneg_right (le_abs_self Cd) hLr)
          have h1 : C1 * Real.log x ≤ |C1| * Real.log x :=
            mul_le_mul_of_nonneg_right (le_abs_self C1) hL0.le
          have h2 : C1 * Real.log x * ((q : ℝ) * max 2 ((b - a) / 2) + x ^ (11 / 20 + ε)) ≤
              |C1| * Real.log x * (3 * x ^ (11 / 20 + ε)) := by
            calc _ ≤ |C1| * Real.log x * ((q : ℝ) * max 2 ((b - a) / 2) + x ^ (11 / 20 + ε)) :=
                  mul_le_mul_of_nonneg_right h1 hqT0
              _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith)
                  (mul_nonneg (abs_nonneg _) hL0.le)
          calc _ ≤ |C1| * Real.log x * (3 * x ^ (11 / 20 + ε)) * _ := mul_le_mul_of_nonneg_right h2 hG0
            _ ≤ _ := mul_le_mul_of_nonneg_left hG'
                (by have := abs_nonneg C1; positivity)
      _ = 3 * |C1| * |Cd| * x ^ (11 / 20 + ε) * (Real.log x * Real.log x ^ (-A - 1)) := by ring
      _ = _ := by rw [hpow1]
  -- the inner boxes, by Lemma 33 with A + 2D in place of A
  have hPi : ∀ i ∈ Finset.range k, ∑ t ∈ S, ‖(Thm4.dirPoly (eL i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ i - β₂ i))
                  (1 : DirichletCharacter ℂ q) (Thm4.half t) *
                Thm4.dirPoly (eM i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t) *
                Thm4.dirPoly (eN i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t))‖ ^ 2 ≤
      |C33| * x ^ (11 / 20 + ε) * Real.log x ^ (-(A + 2 * D)) := by
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    obtain ⟨hreg, hL, hM, hN, h32M, h32N⟩ := hbox i hik
    have := h33 x hx33 q hq1 hqQ a b hab hba S hS hsp (β₁ i) (β₂ i) hreg (eL i) (eM i) (eN i)
      hL hM hN h32M h32N
    refine le_trans this ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hY0)
      (Real.rpow_nonneg hL0.le _)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hpt : ∀ t ∈ S, ‖∑ i ∈ Finset.range k, (Thm4.dirPoly (eL i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ i - β₂ i))
                  (1 : DirichletCharacter ℂ q) (Thm4.half t) *
                Thm4.dirPoly (eM i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t) *
                Thm4.dirPoly (eN i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t)) + (Thm4.dirPoly r c₁ c₂ (x ^ (11 / 20 + ε)) (1 : DirichletCharacter ℂ q) (Thm4.half (t - (a + b) / 2)))‖ ^ 2 ≤
      2 * k * ∑ i ∈ Finset.range k, ‖(Thm4.dirPoly (eL i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ i - β₂ i))
                  (1 : DirichletCharacter ℂ q) (Thm4.half t) *
                Thm4.dirPoly (eM i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t) *
                Thm4.dirPoly (eN i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t))‖ ^ 2 +
        2 * ‖(Thm4.dirPoly r c₁ c₂ (x ^ (11 / 20 + ε)) (1 : DirichletCharacter ℂ q) (Thm4.half (t - (a + b) / 2)))‖ ^ 2 := by
    intro t _
    have h1 := norm_add_le (∑ i ∈ Finset.range k, (Thm4.dirPoly (eL i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ i - β₂ i))
                  (1 : DirichletCharacter ℂ q) (Thm4.half t) *
                Thm4.dirPoly (eM i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t) *
                Thm4.dirPoly (eN i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t))) (Thm4.dirPoly r c₁ c₂ (x ^ (11 / 20 + ε)) (1 : DirichletCharacter ℂ q) (Thm4.half (t - (a + b) / 2)))
    have h2 := norm_sum_le (Finset.range k) (fun i => (Thm4.dirPoly (eL i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ i - β₂ i))
                  (1 : DirichletCharacter ℂ q) (Thm4.half t) *
                Thm4.dirPoly (eM i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t) *
                Thm4.dirPoly (eN i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t)))
    have h3 := sq_sum_le_card_mul_sum_sq (s := Finset.range k)
      (f := fun i => ‖(Thm4.dirPoly (eL i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ i - β₂ i))
                  (1 : DirichletCharacter ℂ q) (Thm4.half t) *
                Thm4.dirPoly (eM i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t) *
                Thm4.dirPoly (eN i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t))‖)
    rw [Finset.card_range] at h3
    have h0 := norm_nonneg (∑ i ∈ Finset.range k, (Thm4.dirPoly (eL i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ i - β₂ i))
                  (1 : DirichletCharacter ℂ q) (Thm4.half t) *
                Thm4.dirPoly (eM i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t) *
                Thm4.dirPoly (eN i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t)))
    have h0' := norm_nonneg (Thm4.dirPoly r c₁ c₂ (x ^ (11 / 20 + ε)) (1 : DirichletCharacter ℂ q) (Thm4.half (t - (a + b) / 2)))
    have h4 : ‖∑ i ∈ Finset.range k, (Thm4.dirPoly (eL i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ i - β₂ i))
                  (1 : DirichletCharacter ℂ q) (Thm4.half t) *
                Thm4.dirPoly (eM i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t) *
                Thm4.dirPoly (eN i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t))‖ ^ 2 ≤
        (∑ i ∈ Finset.range k, ‖(Thm4.dirPoly (eL i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ i - β₂ i))
                  (1 : DirichletCharacter ℂ q) (Thm4.half t) *
                Thm4.dirPoly (eM i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t) *
                Thm4.dirPoly (eN i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t))‖) ^ 2 := pow_le_pow_left₀ h0 h2 2
    have h5 : ‖∑ i ∈ Finset.range k, (Thm4.dirPoly (eL i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ i - β₂ i))
                  (1 : DirichletCharacter ℂ q) (Thm4.half t) *
                Thm4.dirPoly (eM i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t) *
                Thm4.dirPoly (eN i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t)) + (Thm4.dirPoly r c₁ c₂ (x ^ (11 / 20 + ε)) (1 : DirichletCharacter ℂ q) (Thm4.half (t - (a + b) / 2)))‖ ^ 2 ≤
        (‖∑ i ∈ Finset.range k, (Thm4.dirPoly (eL i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ i - β₂ i))
                  (1 : DirichletCharacter ℂ q) (Thm4.half t) *
                Thm4.dirPoly (eM i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t) *
                Thm4.dirPoly (eN i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t))‖ + ‖(Thm4.dirPoly r c₁ c₂ (x ^ (11 / 20 + ε)) (1 : DirichletCharacter ℂ q) (Thm4.half (t - (a + b) / 2)))‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖∑ i ∈ Finset.range k, (Thm4.dirPoly (eL i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ i - β₂ i))
                  (1 : DirichletCharacter ℂ q) (Thm4.half t) *
                Thm4.dirPoly (eM i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t) *
                Thm4.dirPoly (eN i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t))‖ - ‖(Thm4.dirPoly r c₁ c₂ (x ^ (11 / 20 + ε)) (1 : DirichletCharacter ℂ q) (Thm4.half (t - (a + b) / 2)))‖)]
  have hpowk : (k : ℝ) * k * Real.log x ^ (-(A + 2 * D)) ≤ Real.log x ^ (-A) := by
    have e : Real.log x ^ D * Real.log x ^ D * Real.log x ^ (-(A + 2 * D)) =
        Real.log x ^ (-A) := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; congr 1; ring
    rw [← e]
    have hLD : 0 ≤ Real.log x ^ D := Real.rpow_nonneg hL0.le _
    exact mul_le_mul_of_nonneg_right (mul_le_mul hk hk hk0 hLD) (Real.rpow_nonneg hL0.le _)
  rw [Finset.sum_congr rfl fun t ht => by rw [hid t ht]]
  calc _ ≤ ∑ t ∈ S, (2 * k * ∑ i ∈ Finset.range k, ‖(Thm4.dirPoly (eL i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ i - β₂ i))
                  (1 : DirichletCharacter ℂ q) (Thm4.half t) *
                Thm4.dirPoly (eM i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t) *
                Thm4.dirPoly (eN i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t))‖ ^ 2 +
        2 * ‖(Thm4.dirPoly r c₁ c₂ (x ^ (11 / 20 + ε)) (1 : DirichletCharacter ℂ q) (Thm4.half (t - (a + b) / 2)))‖ ^ 2) := Finset.sum_le_sum hpt
    _ = 2 * k * ∑ i ∈ Finset.range k, ∑ t ∈ S, ‖(Thm4.dirPoly (eL i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ i - β₂ i))
                  (1 : DirichletCharacter ℂ q) (Thm4.half t) *
                Thm4.dirPoly (eM i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t) *
                Thm4.dirPoly (eN i) c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂ i) (1 : DirichletCharacter ℂ q)
                  (Thm4.half t))‖ ^ 2 +
        2 * ∑ t ∈ S, ‖(Thm4.dirPoly r c₁ c₂ (x ^ (11 / 20 + ε)) (1 : DirichletCharacter ℂ q) (Thm4.half (t - (a + b) / 2)))‖ ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
    _ ≤ 2 * k * (k * (|C33| * x ^ (11 / 20 + ε) * Real.log x ^ (-(A + 2 * D)))) +
        2 * (3 * |C1| * |Cd| * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by
      gcongr
      calc _ ≤ ∑ i ∈ Finset.range k, |C33| * x ^ (11 / 20 + ε) * Real.log x ^ (-(A + 2 * D)) :=
            Finset.sum_le_sum hPi
        _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = 2 * |C33| * x ^ (11 / 20 + ε) * ((k : ℝ) * k * Real.log x ^ (-(A + 2 * D))) +
        6 * |C1| * |Cd| * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by ring
    _ ≤ 2 * |C33| * x ^ (11 / 20 + ε) * Real.log x ^ (-A) + 6 * |C1| * |Cd| * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
      gcongr
    _ = (2 * |C33| + 6 * |C1| * |Cd|) * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCfin hY0)
        (Real.rpow_nonneg hL0.le _)

end LeanLab.BHP1997.DecompC165d
