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

/-- LEAF. Elementary interval subdivision supporting Jia page 207 and P0089 page 225.
Fixed open windows imply bounds on longer closed windows with positive exponent
slack. This is a general counting statement for a predicate P. -/
theorem extend_windows (P : ℕ → Prop) (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hlocal : ∀ B : ℝ, 0 < B → ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((Ioc ⌊N⌋₊ ⌊N + N ^ a⌋₊).filter P).card : ℝ) ≤ C * N ^ a / Real.log N ^ B) :
    ∀ B : ℝ, 0 < B → ∃ C X₀ : ℝ, ∀ X H : ℝ, X₀ ≤ X → X ^ b ≤ H → H ≤ X →
      (((Icc ⌈X⌉₊ ⌊X + H⌋₊).filter P).card : ℝ) ≤ C * H / Real.log X ^ B := by sorry

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
