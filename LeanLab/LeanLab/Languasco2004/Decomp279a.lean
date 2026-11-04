/-
Jia 1996, https://doi.org/10.4064/aa-77-3-207-287, pages 207 to 287.
AI wrote the Lean code. Goldbach is open. Analytic leaves stay OPEN.
-/
import LeanLab.Languasco2004.StatementsA

namespace LeanLab.Languasco2004.Decomp279a
open Finset Real LeanLab.Languasco2004.EncA
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 208: the basic interval length A. -/
def windowLength (N ε : ℝ) : ℝ := N ^ (7 / 108 + 12 * ε)
/-- Page 208: the localization length Y. -/
def localization (N ε : ℝ) : ℝ := N ^ (7 / 12 + ε)
/-- Page 263: even integers in the basic interval, open at its left end. -/
def window (N ε : ℝ) : Finset ℕ :=
  (Ioc ⌊N⌋₊ ⌊N + windowLength N ε⌋₊).filter Even
/-- Page 262 display 43: the restricted prime representation count T. -/
def representations (N Y : ℝ) (n : ℕ) : ℕ :=
  ((range (n + 1)).filter (fun p : ℕ => p.Prime ∧ (n - p).Prime ∧
    N - Y < (p : ℝ) ∧ (p : ℝ) ≤ N ∧ ((n - p : ℕ) : ℝ) ≤ 2 * Y)).card
/-- Page 262 display 45: the singular factor C of n. -/
def singular (n : ℕ) : ℝ :=
  (∏' p : Nat.Primes, if (p : ℕ) ∣ n then 1 else
    1 - 1 / ((p : ℝ) - 1) ^ 2) *
  ∏ p ∈ n.primeFactors, (1 + 1 / ((p : ℝ) - 1))
/-- Page 262 display 44: the common main term. -/
def scale (N Y : ℝ) (n : ℕ) : ℝ := singular n * Y / (Real.log Y * Real.log N)
/-- Pages 262 and 263: S of A_d and z. Every prime dividing d is at least z
in the uses below, so sifting a or a divided by d gives the same count. -/
def sifted (N Y : ℝ) (n d : ℕ) (z : ℝ) : ℕ :=
  ((Icc 1 n).filter (fun a => d ∣ a ∧ (n - a).Prime ∧
    N - Y < ((n - a : ℕ) : ℝ) ∧ ((n - a : ℕ) : ℝ) ≤ N ∧
    ∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬ p ∣ n → ¬ p ∣ a)).card
/-- Page 263 Lemma 22: the initial sifted term. -/
def initial (N Y : ℝ) (n : ℕ) : ℝ := sifted N Y n 1 (Y ^ (16 / 135 : ℝ))
/-- Page 265 Lemma 23: the single prime subtraction term. -/
def subtraction (N Y : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime ∧
    Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y)),
    (sifted N Y n p (Y ^ (16 / 135 : ℝ)) : ℝ)
/-- Page 267 display 52: the double prime recovery term Omega. -/
def recovery (N Y : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime ∧
    Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y)),
    ∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
      Y ^ (16 / 135 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ)))),
      (sifted N Y n (p * q) q : ℝ)

/-- LEAF. Page 263 Lemma 22, proved on pages 263 to 265.
The exceptional set is the set of failures of this single sieve bound. -/
theorem initial_bound :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        initial N (localization N ε) n < 4.735124 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- LEAF. Page 265 Lemma 23, proved on pages 265 to 267.
This leaf controls the failures of the single subtraction bound. -/
theorem subtraction_bound :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        6.822470 * scale N (localization N ε) n < subtraction N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- LEAF. Page 286 display 65, proved by Lemmas 24 to 28 on pages 269 to 286.
Only the double sieve recovery term occurs in this leaf. -/
theorem recovery_bound :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        recovery N (localization N ε) n < 2.104057 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- LEAF. Page 263 displays 46 and 47 and page 286 final subtraction.
The elementary Buchstab identity has its error absorbed into 0.005 of the
positive main term. Cutoff boundary terms are absorbed too.
This leaf asserts no bound for any of the three sieve terms. -/
theorem representation_bridge :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → ∀ n ∈ window N ε,
      0 < scale N (localization N ε) n ∧
      initial N (localization N ε) n - subtraction N (localization N ε) n +
        recovery N (localization N ε) n - 0.005 * scale N (localization N ε) n ≤
        (representations N (localization N ε) n : ℝ) := by sorry

/-- The rpow/log comparison used per block: for `1 ≤ N`, `X/2 ≤ N ≤ 3X` and `4 ≤ X`,
`N^a / log N^B ≤ 3^a * 2^B * X^a / log X^B`. -/
private lemma rpow_log_div_le {a B X N : ℝ} (ha : 0 < a) (hB : 0 < B) (hX : 1 ≤ X)
    (hX4 : 4 ≤ X) (hN1 : 1 ≤ N) (hNlo : X / 2 ≤ N) (hNhi : N ≤ 3 * X) :
    N ^ a / Real.log N ^ B ≤ 3 ^ a * 2 ^ B * X ^ a / Real.log X ^ B := by
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN1
  have hX0 : 0 < X := by linarith
  have hNa : N ^ a ≤ 3 ^ a * X ^ a := by
    have h1 : N ^ a ≤ (3 * X) ^ a := Real.rpow_le_rpow hN0.le hNhi ha.le
    rwa [Real.mul_rpow (by norm_num) hX0.le] at h1
  have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogN : Real.log X / 2 ≤ Real.log N := by
    have h1 : Real.log (X / 2) ≤ Real.log N := Real.log_le_log (by linarith) hNlo
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    have h2 : Real.log 2 ≤ Real.log X / 2 := by
      have h3 : Real.log 4 ≤ Real.log X := Real.log_le_log (by norm_num) hX4
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h3
      norm_num at h3
      linarith
    linarith
  have hlogNpos : 0 < Real.log N := lt_of_lt_of_le (by linarith) hlogN
  have h2Bpos : (0 : ℝ) < 2 ^ B := Real.rpow_pos_of_pos (by norm_num) B
  have hlogXN : Real.log X ^ B ≤ 2 ^ B * Real.log N ^ B := by
    have h1 : (Real.log X / 2) ^ B ≤ Real.log N ^ B :=
      Real.rpow_le_rpow (by positivity) hlogN hB.le
    rw [Real.div_rpow hlogXpos.le (by norm_num)] at h1
    have h2 : 2 ^ B * (Real.log X ^ B / 2 ^ B) = Real.log X ^ B := by
      rw [mul_comm (2 ^ B) (Real.log X ^ B / 2 ^ B)]
      exact div_mul_cancel₀ _ (ne_of_gt h2Bpos)
    have h3 := mul_le_mul_of_nonneg_left h1 h2Bpos.le
    linarith [h2, h3]
  rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hlogNpos B) (Real.rpow_pos_of_pos hlogXpos B)]
  have hmain : N ^ a * Real.log X ^ B ≤ (3 ^ a * X ^ a) * (2 ^ B * Real.log N ^ B) :=
    mul_le_mul hNa hlogXN (le_of_lt (Real.rpow_pos_of_pos hlogXpos B)) (by positivity)
  calc N ^ a * Real.log X ^ B ≤ (3 ^ a * X ^ a) * (2 ^ B * Real.log N ^ B) := hmain
    _ = (3 ^ a * 2 ^ B * X ^ a) * Real.log N ^ B := by ring

/-- LEAF. Elementary interval subdivision supporting Jia page 207 and P0089 page 225.
Fixed open windows imply bounds on longer closed windows with positive exponent
slack. This is a general counting statement for a predicate P. -/
theorem extend_windows (P : ℕ → Prop) (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hlocal : ∀ B : ℝ, 0 < B → ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((Ioc ⌊N⌋₊ ⌊N + N ^ a⌋₊).filter P).card : ℝ) ≤ C * N ^ a / Real.log N ^ B) :
    ∀ B : ℝ, 0 < B → ∃ C X₀ : ℝ, ∀ X H : ℝ, X₀ ≤ X → X ^ b ≤ H → H ≤ X →
      (((Icc ⌈X⌉₊ ⌊X + H⌋₊).filter P).card : ℝ) ≤ C * H / Real.log X ^ B := by
  intro B hB
  obtain ⟨C, N₀, hC⟩ := hlocal B hB
  set C₀ : ℝ := max C 0 with hC₀def
  have hC₀nonneg : 0 ≤ C₀ := by rw [hC₀def]; exact le_max_right _ _
  have hCC : C ≤ C₀ := by rw [hC₀def]; exact le_max_left _ _
  have hbpos : 0 < b := lt_trans ha hab
  -- eventual inequality log X ^ B ≤ X ^ b
  have hlogev : ∀ᶠ X : ℝ in Filter.atTop, Real.log X ^ B ≤ X ^ b := by
    have hbB : 0 < b / B := div_pos hbpos hB
    have h1 : Real.log =o[Filter.atTop] (fun x : ℝ => x ^ (b / B)) :=
      isLittleO_log_rpow_atTop hbB
    filter_upwards [h1.eventuallyLE, Filter.eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx1
    have hlognn : 0 ≤ Real.log x := Real.log_nonneg hx1.le
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlognn,
      abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at hx
    calc Real.log x ^ B ≤ (x ^ (b / B)) ^ B := Real.rpow_le_rpow hlognn hx hB.le
      _ = x ^ b := by
            rw [← Real.rpow_mul hx0.le]
            congr 1
            field_simp
  rw [Filter.eventually_atTop] at hlogev
  obtain ⟨X₁, hX₁⟩ := hlogev
  set X₀ : ℝ := max (max (N₀ + 2) X₁) (max 4 (8 ^ (1 / a))) with hX₀def
  refine ⟨25 * C₀ * 3 ^ a * 2 ^ B + 1, X₀, ?_⟩
  intro X H hX hXb hHX
  rw [hX₀def] at hX
  have hX4 : 4 ≤ X :=
    le_trans (le_trans (le_max_left (4 : ℝ) (8 ^ (1 / a)))
      (le_max_right (max (N₀ + 2) X₁) (max 4 (8 ^ (1 / a))))) hX
  have hX8a : 8 ^ (1 / a) ≤ X :=
    le_trans (le_trans (le_max_right (4 : ℝ) (8 ^ (1 / a)))
      (le_max_right (max (N₀ + 2) X₁) (max 4 (8 ^ (1 / a))))) hX
  have hXN₀ : N₀ + 2 ≤ X :=
    le_trans (le_trans (le_max_left (N₀ + 2) X₁)
      (le_max_left (max (N₀ + 2) X₁) (max 4 (8 ^ (1 / a))))) hX
  have hXX₁ : X₁ ≤ X :=
    le_trans (le_trans (le_max_right (N₀ + 2) X₁)
      (le_max_left (max (N₀ + 2) X₁) (max 4 (8 ^ (1 / a))))) hX
  have hX1le : 1 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hlogXB : Real.log X ^ B ≤ X ^ b := hX₁ X hXX₁
  have hHpos : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos b) hXb
  have hH1 : 1 ≤ H := (Real.one_le_rpow hX1le hbpos.le).trans hXb
  have hXaH : X ^ a ≤ H :=
    (Real.rpow_le_rpow_of_exponent_le hX1le (le_of_lt hab)).trans hXb
  have hXa8 : 8 ≤ X ^ a := by
    have h1 : ((8 : ℝ) ^ (1 / a)) ^ a = 8 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8), div_mul_cancel₀ _ (ne_of_gt ha),
        Real.rpow_one]
    have h2 : ((8 : ℝ) ^ (1 / a)) ^ a ≤ X ^ a :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hX8a ha.le
    rwa [h1] at h2
  -- the block length, the number of blocks, and the left end
  set m : ℕ := ⌊X⌋₊ with hmdef
  have hmle : (m : ℝ) ≤ X := by rw [hmdef]; exact Nat.floor_le hXpos.le
  have hmgt : X - 1 < (m : ℝ) := by rw [hmdef]; linarith [Nat.lt_floor_add_one X]
  have hmge : X / 2 ≤ (m : ℝ) := by linarith
  set L : ℕ := ⌊X ^ a / 4⌋₊ with hLdef
  have hLle : (L : ℝ) ≤ X ^ a / 4 := by
    rw [hLdef]; exact Nat.floor_le (by positivity)
  have hLgt : X ^ a / 4 - 1 < (L : ℝ) := by
    rw [hLdef]; linarith [Nat.lt_floor_add_one (X ^ a / 4)]
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    apply Nat.le_floor
    rw [Nat.cast_one]
    linarith
  have hLpos : 0 < L := hL1
  have hLposR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLposR
  have hLXa : (L : ℝ) ≤ X ^ a / 4 := hLle
  set k : ℕ := ⌈(H + 2) / (L : ℝ)⌉₊ with hkdef
  have hkL : H + 2 ≤ (k : ℝ) * L := by
    have h := Nat.le_ceil ((H + 2) / (L : ℝ))
    have h2 := (div_le_iff₀ hLposR).mp h
    simpa only [hkdef] using h2
  have hkub : (k : ℝ) ≤ (H + 2) / (L : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ (H + 2) / (L : ℝ) := by positivity
    have h := Nat.ceil_lt_add_one h0
    have : (k : ℝ) < (H + 2) / (L : ℝ) + 1 := by simpa only [hkdef] using h
    linarith
  have hk1 : 1 ≤ k := by
    have h1 : (L : ℝ) ≤ H + 2 := by linarith [hLle, hXaH, hL1]
    have hkne : k ≠ 0 := by
      intro h0
      rw [h0] at hkL
      simp only [Nat.cast_zero, zero_mul] at hkL
      linarith [hLposR]
    omega
  -- the cover
  have hcover : (Icc ⌈X⌉₊ ⌊X + H⌋₊).filter P ⊆
      insert ⌈X⌉₊ ((range k).biUnion (fun j =>
        (Ioc (m + j * L) (m + (j + 1) * L)).filter P)) := by
    intro n hn
    rw [mem_filter, mem_Icc] at hn
    obtain ⟨⟨hlo, hhi⟩, hP⟩ := hn
    rw [mem_insert]
    rcases eq_or_ne n ⌈X⌉₊ with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rw [mem_biUnion]
      have hmlt : m < n := by
        have hmc : m ≤ ⌈X⌉₊ := Nat.floor_le_ceil X
        omega
      have ht2 : (((n - m - 1 : ℕ)) : ℝ) < H + 2 := by
        have h1 : (n : ℝ) ≤ X + H :=
          le_trans (by exact_mod_cast hhi) (Nat.floor_le (by linarith))
        have h2 : (((n - m - 1 : ℕ)) : ℝ) = (n : ℝ) - (m : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n - m), Nat.cast_sub (by omega : m ≤ n)]
          push_cast
          ring
        rw [h2]
        linarith
      set j : ℕ := (n - m - 1) / L with hjdef
      set r : ℕ := (n - m - 1) % L with hrdef
      have htj : j * L + r = n - m - 1 := by
        rw [hjdef, hrdef, mul_comm]
        exact Nat.div_add_mod (n - m - 1) L
      have hrL : r < L := by rw [hrdef]; exact Nat.mod_lt _ hLpos
      refine ⟨j, ?_, ?_⟩
      · rw [mem_range]
        have hltR : (((j * L : ℕ)) : ℝ) < (k : ℝ) * L := by
          have ht1 : (((j * L : ℕ)) : ℝ) ≤ (((n - m - 1 : ℕ)) : ℝ) := by
            exact_mod_cast (by omega : j * L ≤ n - m - 1)
          linarith [ht1, ht2, hkL]
        have hlt : j * L < k * L := by exact_mod_cast hltR
        exact (Nat.mul_lt_mul_right hLpos).mp hlt
      · rw [mem_filter]
        refine ⟨?_, hP⟩
        rw [mem_Ioc]
        constructor
        · have h1 : m + j * L ≤ n - 1 := by omega
          omega
        · have h1 : n ≤ m + (j * L + L) := by omega
          have h2 : (j + 1) * L = j * L + L := by ring
          omega
  have hcard1 : ((Icc ⌈X⌉₊ ⌊X + H⌋₊).filter P).card ≤
      ((range k).biUnion (fun j =>
        (Ioc (m + j * L) (m + (j + 1) * L)).filter P)).card + 1 :=
    (card_le_card hcover).trans (card_insert_le _ _)
  have hcard2 : (((range k).biUnion (fun j =>
        (Ioc (m + j * L) (m + (j + 1) * L)).filter P)).card : ℝ) ≤
      ∑ j ∈ range k, (((Ioc (m + j * L) (m + (j + 1) * L)).filter P).card : ℝ) := by
    have h := card_biUnion_le (s := range k)
      (t := fun j => (Ioc (m + j * L) (m + (j + 1) * L)).filter P)
    exact_mod_cast h
  have hterm : ∀ j ∈ range k, (((Ioc (m + j * L) (m + (j + 1) * L)).filter P).card : ℝ) ≤
      C₀ * 3 ^ a * 2 ^ B * X ^ a / Real.log X ^ B := by
    intro j hj
    have hjk : j < k := mem_range.mp hj
    have hjL : (j : ℝ) * L ≤ H + 2 := by
      have hjk1 : j ≤ k - 1 := by omega
      have h1 : ((j : ℕ) : ℝ) * L ≤ ((k - 1 : ℕ) : ℝ) * L := by
        have : (j : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hjk1
        exact mul_le_mul_of_nonneg_right this hLposR.le
      have h2 : ((k - 1 : ℕ) : ℝ) * L < H + 2 := by
        have hku : (k : ℝ) < (H + 2) / (L : ℝ) + 1 := by
          have h0 : (0 : ℝ) ≤ (H + 2) / (L : ℝ) := by positivity
          have h := Nat.ceil_lt_add_one h0
          have : (k : ℝ) < (H + 2) / (L : ℝ) + 1 := by simpa only [hkdef] using h
          linarith
        have h3 : (k : ℝ) - 1 < (H + 2) / (L : ℝ) := by linarith
        have h4 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
          rw [Nat.cast_sub hk1]
          norm_num
        rw [h4]
        exact (lt_div_iff₀ hLposR).mp h3
      linarith
    have hNhi : (((m + j * L : ℕ)) : ℝ) ≤ 3 * X := by
      have hcast : (((m + j * L : ℕ)) : ℝ) = (m : ℝ) + (j : ℝ) * L := by push_cast; ring
      rw [hcast]
      linarith [hmle, hjL, hHX]
    have hNlo : X / 2 ≤ (((m + j * L : ℕ)) : ℝ) := by
      have hcast : (((m + j * L : ℕ)) : ℝ) = (m : ℝ) + (j : ℝ) * L := by push_cast; ring
      rw [hcast]
      have : (0 : ℝ) ≤ (j : ℝ) * L := by positivity
      linarith
    have hN1 : 1 ≤ (((m + j * L : ℕ)) : ℝ) := by
      have hcast : (((m + j * L : ℕ)) : ℝ) = (m : ℝ) + (j : ℝ) * L := by push_cast; ring
      rw [hcast]
      linarith [hmge, hX4]
    have hN₀le : N₀ ≤ (((m + j * L : ℕ)) : ℝ) := by
      have hcast : (((m + j * L : ℕ)) : ℝ) = (m : ℝ) + (j : ℝ) * L := by push_cast; ring
      rw [hcast]
      have : N₀ ≤ (m : ℝ) := by linarith
      have : (0 : ℝ) ≤ (j : ℝ) * L := by positivity
      linarith
    have hloc := hC (((m + j * L : ℕ)) : ℝ) hN₀le
    simp only [Nat.floor_natCast] at hloc
    have hLpow : (L : ℝ) ≤ (((m + j * L : ℕ)) : ℝ) ^ a := by
      have h2 : X ^ a / 4 ≤ (X / 2) ^ a := by
        rw [Real.div_rpow hXpos.le (by norm_num)]
        have h2a : (2 : ℝ) ^ a ≤ 4 := by
          have h3 := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
            (by linarith : a ≤ 2)
          norm_num at h3
          linarith
        rw [div_le_div_iff₀ (by norm_num) (Real.rpow_pos_of_pos (by norm_num) a)]
        nlinarith [Real.rpow_pos_of_pos hXpos a]
      have h3 : (X / 2) ^ a ≤ (((m + j * L : ℕ)) : ℝ) ^ a :=
        Real.rpow_le_rpow (by positivity) (by linarith [hmge]) ha.le
      linarith
    have hfloor : m + (j + 1) * L ≤ ⌊(((m + j * L : ℕ)) : ℝ) +
        (((m + j * L : ℕ)) : ℝ) ^ a⌋₊ := by
      apply Nat.le_floor
      have hcast : (((m + (j + 1) * L : ℕ)) : ℝ) = (((m + j * L : ℕ)) : ℝ) + (L : ℝ) := by
        push_cast; ring
      rw [hcast]
      linarith
    have hsub : (Ioc (m + j * L) (m + (j + 1) * L)).filter P ⊆
        (Ioc (m + j * L) ⌊(((m + j * L : ℕ)) : ℝ) +
          (((m + j * L : ℕ)) : ℝ) ^ a⌋₊).filter P := by
      apply filter_subset_filter
      intro n hn
      rw [mem_Ioc] at hn ⊢
      obtain ⟨h1, h2⟩ := hn
      exact ⟨h1, le_trans h2 hfloor⟩
    have hcard_le : (((Ioc (m + j * L) (m + (j + 1) * L)).filter P).card : ℝ) ≤
        (((Ioc (m + j * L) ⌊(((m + j * L : ℕ)) : ℝ) +
          (((m + j * L : ℕ)) : ℝ) ^ a⌋₊).filter P).card : ℝ) :=
      Nat.cast_le.mpr (card_le_card hsub)
    have hCC' : C * (((m + j * L : ℕ)) : ℝ) ^ a / Real.log (((m + j * L : ℕ)) : ℝ) ^ B ≤
        C₀ * (((m + j * L : ℕ)) : ℝ) ^ a / Real.log (((m + j * L : ℕ)) : ℝ) ^ B := by
      apply div_le_div_of_nonneg_right _ (le_of_lt ?_)
      · exact mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg (by positivity) a)
      · exact Real.rpow_pos_of_pos (Real.log_pos (by linarith [hN1])) B
    have hrp := rpow_log_div_le ha hB hX1le hX4 hN1 hNlo hNhi
    calc (((Ioc (m + j * L) (m + (j + 1) * L)).filter P).card : ℝ)
        ≤ C * (((m + j * L : ℕ)) : ℝ) ^ a / Real.log (((m + j * L : ℕ)) : ℝ) ^ B :=
          hcard_le.trans hloc
      _ ≤ C₀ * (((m + j * L : ℕ)) : ℝ) ^ a / Real.log (((m + j * L : ℕ)) : ℝ) ^ B := hCC'
      _ = C₀ * ((((m + j * L : ℕ)) : ℝ) ^ a / Real.log (((m + j * L : ℕ)) : ℝ) ^ B) := by
          rw [mul_div_assoc]
      _ ≤ C₀ * (3 ^ a * 2 ^ B * X ^ a / Real.log X ^ B) :=
          mul_le_mul_of_nonneg_left hrp hC₀nonneg
      _ = C₀ * 3 ^ a * 2 ^ B * X ^ a / Real.log X ^ B := by
          rw [mul_div_assoc]
          ring
  have hLX : X ^ a / (L : ℝ) ≤ 8 := by
    have hXapos : 0 < X ^ a := Real.rpow_pos_of_pos hXpos a
    have hLge : X ^ a / 8 ≤ (L : ℝ) := by linarith [hLgt, hXa8]
    rw [div_le_iff₀ hLposR]
    linarith
  have hkX : (k : ℝ) * X ^ a ≤ 25 * H := by
    have h1 : (k : ℝ) * X ^ a ≤ ((H + 2) / (L : ℝ) + 1) * X ^ a :=
      mul_le_mul_of_nonneg_right hkub (Real.rpow_nonneg hXpos.le a)
    have h2 : ((H + 2) / (L : ℝ) + 1) * X ^ a = (H + 2) * (X ^ a / (L : ℝ)) + X ^ a := by
      field_simp
    have h3 : (H + 2) * (X ^ a / (L : ℝ)) + X ^ a ≤ 25 * H := by nlinarith [hLX, hXaH, hH1]
    linarith
  have hlogposX : 0 < Real.log X ^ B := Real.rpow_pos_of_pos (Real.log_pos (by linarith)) B
  have hSnonneg : 0 ≤ C₀ * 3 ^ a * 2 ^ B :=
    mul_nonneg (mul_nonneg hC₀nonneg (Real.rpow_nonneg (by norm_num) a))
      (Real.rpow_nonneg (by norm_num) B)
  have hSlog : 0 ≤ C₀ * 3 ^ a * 2 ^ B / Real.log X ^ B := div_nonneg hSnonneg hlogposX.le
  have hfinal : (1 : ℝ) ≤ H / Real.log X ^ B := by
    rw [le_div_iff₀ hlogposX]
    linarith
  have hcard3 : (((Icc ⌈X⌉₊ ⌊X + H⌋₊).filter P).card : ℝ) ≤
      1 + (k : ℝ) * (C₀ * 3 ^ a * 2 ^ B * X ^ a / Real.log X ^ B) := by
    have h1 : (((Icc ⌈X⌉₊ ⌊X + H⌋₊).filter P).card : ℝ) ≤
        (((range k).biUnion (fun j =>
          (Ioc (m + j * L) (m + (j + 1) * L)).filter P)).card : ℝ) + 1 := by
      exact_mod_cast hcard1
    have h2 : (((range k).biUnion (fun j =>
          (Ioc (m + j * L) (m + (j + 1) * L)).filter P)).card : ℝ) ≤
        ∑ j ∈ range k, (C₀ * 3 ^ a * 2 ^ B * X ^ a / Real.log X ^ B) :=
      hcard2.trans (sum_le_sum hterm)
    have h3 : (∑ j ∈ range k, (C₀ * 3 ^ a * 2 ^ B * X ^ a / Real.log X ^ B))
        = (k : ℝ) * (C₀ * 3 ^ a * 2 ^ B * X ^ a / Real.log X ^ B) := by
      rw [sum_const, card_range, nsmul_eq_mul]
    linarith [h1, h2, h3]
  calc (((Icc ⌈X⌉₊ ⌊X + H⌋₊).filter P).card : ℝ)
      ≤ 1 + (k : ℝ) * (C₀ * 3 ^ a * 2 ^ B * X ^ a / Real.log X ^ B) := hcard3
    _ = 1 + ((k : ℝ) * X ^ a) * (C₀ * 3 ^ a * 2 ^ B / Real.log X ^ B) := by
          field_simp
    _ ≤ H / Real.log X ^ B + (25 * H) * (C₀ * 3 ^ a * 2 ^ B / Real.log X ^ B) := by
          have ha2 : ((k : ℝ) * X ^ a) * (C₀ * 3 ^ a * 2 ^ B / Real.log X ^ B) ≤
              (25 * H) * (C₀ * 3 ^ a * 2 ^ B / Real.log X ^ B) :=
            mul_le_mul_of_nonneg_right hkX hSlog
          linarith
    _ = (25 * C₀ * 3 ^ a * 2 ^ B + 1) * H / Real.log X ^ B := by
          field_simp
          ring


/-- Page 262 display 43: a positive restricted count supplies a Goldbach sum. -/
theorem goldbach_of_representations {N Y : ℝ} {n : ℕ}
    (h : 0 < representations N Y n) : IsGoldbachSum n := by
  obtain ⟨p, hp⟩ := Finset.card_pos.mp h
  obtain ⟨hpRange, hpPrime, hqPrime, _⟩ := Finset.mem_filter.mp hp
  exact ⟨p, n - p, hpPrime, hqPrime,
    Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hpRange))⟩

/-- Page 286: the numerical sieve margin is positive after the error. -/
theorem positive_margin (u v w s t : ℝ) (hs : 0 < s)
    (hu : 4.735124 * s ≤ u) (hv : v ≤ 6.822470 * s)
    (hw : 2.104057 * s ≤ w) (ht : u - v + w - 0.005 * s ≤ t) : 0 < t := by linarith

/-- Page 286: the union of the three sieve exceptional sets retains the log bound.
CONDITIONAL ON the three analytic bounds and representation_bridge. -/
theorem local_exception_bound :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((Ioc ⌊N⌋₊ ⌊N + windowLength N ε⌋₊).filter
        (fun n => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨ε₁, he₁, hi⟩ := initial_bound
  obtain ⟨ε₂, he₂, hj⟩ := subtraction_bound
  obtain ⟨ε₃, he₃, hk⟩ := recovery_bound
  obtain ⟨ε₄, he₄, hl⟩ := representation_bridge
  refine ⟨min (min ε₁ ε₂) (min ε₃ ε₄), lt_min (lt_min he₁ he₂) (lt_min he₃ he₄), ?_⟩
  intro ε B hε hεsmall hB
  have hε₁ : ε < ε₁ := hεsmall.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hε₂ : ε < ε₂ := hεsmall.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hε₃ : ε < ε₃ := hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hε₄ : ε < ε₄ := hεsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C₁, N₁, h₁⟩ := hi ε B hε hε₁ hB
  obtain ⟨C₂, N₂, h₂⟩ := hj ε B hε hε₂ hB
  obtain ⟨C₃, N₃, h₃⟩ := hk ε B hε hε₃ hB
  obtain ⟨N₄, h₄⟩ := hl ε hε hε₄
  refine ⟨C₁ + C₂ + C₃, max (max N₁ N₂) (max N₃ N₄), ?_⟩
  intro N hN
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN₃ : N₃ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₄ : N₄ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  let bad₁ := (window N ε).filter (fun n =>
    initial N (localization N ε) n < 4.735124 * scale N (localization N ε) n)
  let bad₂ := (window N ε).filter (fun n =>
    6.822470 * scale N (localization N ε) n < subtraction N (localization N ε) n)
  let bad₃ := (window N ε).filter (fun n =>
    recovery N (localization N ε) n < 2.104057 * scale N (localization N ε) n)
  have hsub : ((Ioc ⌊N⌋₊ ⌊N + windowLength N ε⌋₊).filter
      (fun n => Even n ∧ ¬ IsGoldbachSum n)) ⊆ (bad₁ ∪ bad₂) ∪ bad₃ := by
    intro n hn
    obtain ⟨hnI, hne, hng⟩ := Finset.mem_filter.mp hn
    have hnw : n ∈ window N ε := Finset.mem_filter.mpr ⟨hnI, hne⟩
    by_contra hnBad
    have hb₁ : ¬ n ∈ bad₁ := fun h => hnBad (mem_union.mpr (Or.inl (mem_union.mpr (Or.inl h))))
    have hb₂ : ¬ n ∈ bad₂ := fun h => hnBad (mem_union.mpr (Or.inl (mem_union.mpr (Or.inr h))))
    have hb₃ : ¬ n ∈ bad₃ := fun h => hnBad (mem_union.mpr (Or.inr h))
    have hu : 4.735124 * scale N (localization N ε) n ≤ initial N (localization N ε) n :=
      le_of_not_gt (fun h => hb₁ (mem_filter.mpr ⟨hnw, h⟩))
    have hv : subtraction N (localization N ε) n ≤ 6.822470 * scale N (localization N ε) n :=
      le_of_not_gt (fun h => hb₂ (mem_filter.mpr ⟨hnw, h⟩))
    have hw : 2.104057 * scale N (localization N ε) n ≤ recovery N (localization N ε) n :=
      le_of_not_gt (fun h => hb₃ (mem_filter.mpr ⟨hnw, h⟩))
    obtain ⟨hs, ht⟩ := h₄ N hN₄ n hnw
    have hpos := positive_margin _ _ _ _ _ hs hu hv hw ht
    exact hng (goldbach_of_representations (by exact_mod_cast hpos))
  have hcard := (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hcardR : (((Ioc ⌊N⌋₊ ⌊N + windowLength N ε⌋₊).filter
      (fun n => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ) ≤
      (bad₁.card : ℝ) + bad₂.card + bad₃.card := by exact_mod_cast hcard
  have hsum := add_le_add (add_le_add (h₁ N hN₁) (h₂ N hN₂)) (h₃ N hN₃)
  calc _ ≤ (bad₁.card : ℝ) + bad₂.card + bad₃.card := hcardR
       _ ≤ C₁ * windowLength N ε / Real.log N ^ B +
         C₂ * windowLength N ε / Real.log N ^ B +
         C₃ * windowLength N ε / Real.log N ^ B := hsum
       _ = _ := by ring

/-- The exact statement of EncA.jia from five smaller OPEN leaves.
CONDITIONAL ON initial_bound, subtraction_bound, recovery_bound,
representation_bridge and extend_windows. -/
theorem jia_from_leaves : Theorem1_5 := by
  intro ε hε
  let b : ℝ := min (7 / 108 + ε) (1 / 2)
  obtain ⟨ε₀, he₀, hlocal⟩ := local_exception_bound
  let η : ℝ := min (min (ε / 24) (1 / 2000)) (ε₀ / 2)
  have hη : 0 < η := lt_min (lt_min (by positivity) (by norm_num)) (by positivity)
  have hηsmall : η < ε₀ := (min_le_right _ _).trans_lt (by linarith)
  have hηε : η ≤ ε / 24 := (min_le_left _ _).trans (min_le_left _ _)
  have hηcap : η ≤ 1 / 2000 := (min_le_left _ _).trans (min_le_right _ _)
  have ha : (0 : ℝ) < 7 / 108 + 12 * η := by positivity
  have hab : 7 / 108 + 12 * η < b := by
    apply lt_min
    · linarith
    · linarith
  have hb : b < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hext := extend_windows (fun n => Even n ∧ ¬ IsGoldbachSum n)
    (7 / 108 + 12 * η) b ha hab hb
    (fun B hB => by
      obtain ⟨C, N₀, hC⟩ := hlocal η B hη hηsmall hB
      refine ⟨C, N₀, ?_⟩
      intro N hN
      convert hC N hN using 1 <;> unfold windowLength <;> congr 2 <;> ext n <;> simp)
  apply LogFrom_mono (r := b) (min_le_left _ _)
  intro B hB
  obtain ⟨C, X₀, hC⟩ := hext B hB
  refine ⟨C, X₀, ?_⟩
  intro X H hX hH hHu
  convert hC X H hX hH hHu using 1
  unfold LeanLab.LanguascoPerelli1996.EH
  congr 2
  ext n
  simp

#print axioms initial_bound
#print axioms subtraction_bound
#print axioms recovery_bound
#print axioms representation_bridge
#print axioms extend_windows
#print axioms goldbach_of_representations
#print axioms positive_margin
#print axioms local_exception_bound
#print axioms jia_from_leaves
end
end LeanLab.Languasco2004.Decomp279a
