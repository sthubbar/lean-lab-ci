/-
P0056 P. Xi, "Sumsets in primes containing almost all even positive integers",
arXiv 1206.2148. Encoded from v1, 11 Jun 2012. The arXiv abstract page says v2, 28 Jul 2012,
is a withdrawal: "This paper has been withdrawn by the author". See the WARNING below.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
Nothing here is cited with `sorry`, because the paper is withdrawn; the theorems are `def`s,
and every `theorem` below is proved with zero sorry.

Asymptotic notation. Every `≪` and `O(...)` of the paper is written with an explicit
existential constant `C`, quantified after the family `A` and the density `δ`, so `C` may
depend on them; the paper says the constant depends on `c₀` and `η`, and its proof also uses
the implied constants of hypothesis (3). The quantity `x` of the paper is a natural number
`x` here, and the set `A ⊆ P ∩ [1, x]` is a family `A x` indexed by `x`.

WARNING. The paper is withdrawn. Theorems 1 and 2 are encoded as printed, but the
encoder suspects Theorem 2 is false: if `A x` is the set of primes `p ≤ x` with
`{p √2} < 1/4`, Vinogradov's equidistribution of `p √2` in progressions suggests that `A`
meets hypothesis (3) with `δ = 1/4`, while `fract_sum_lt_half` and `excSet_of_fract` below
prove that no even `n` with `{n √2} ≥ 1/2` is in `A + A`, so `E(x)` has about `x / 4`
elements. The equidistribution step is NOT formalized here.
-/
import Mathlib
import LeanLab.Common.Goldbach

namespace LeanLab.Xi2012

open Finset Real

/-! ### Notation of the paper -/

/-- `ϑ_X(y; q, a) = ∑_{p ∈ X, p ≤ y, p ≡ a (mod q)} log p`, the congruence on `ℕ`.
Re-encoded 2026-10-19 by CLOUD 20261019T0514Z-cloud17, U-5213, see AUDIT.md. -/
noncomputable def theta (X : Finset ℕ) (y : ℝ) (q a : ℕ) : ℝ := by
  classical
  exact ∑ p ∈ X.filter (fun p : ℕ => (p : ℝ) ≤ y ∧ p % q = a % q), Real.log p

/-- SUPERSEDED, kept for the audit record: the first encoding of `ϑ`, where the finset was cast
to `ℝ` and `%` became the real remainder, always `0`, so the congruence is void. Proved
misencoded in LeanLab/PNTPort/PsiChi/XiLink.lean, U-5212. -/
noncomputable def thetaReal (X : Finset ℕ) (y : ℝ) (q a : ℕ) : ℝ := by
  classical
  exact ∑ p ∈ X.filter (fun p => (p : ℝ) ≤ y ∧ p % q = a % q), Real.log p

/-- `A x ⊆ P ∩ [1, x]` for every `x`. -/
def IsPrimeFamily (A : ℕ → Finset ℕ) : Prop :=
  ∀ x p, p ∈ A x → p.Prime ∧ p ≤ x

/-- Hypothesis (3), the Siegel-Walfisz condition: for every `c > 0` there is `C` with
`|ϑ_A(y; q, a) - δ y / φ(q)| ≤ C x (log x)^(-2c)` for all `y ≤ x`, all `q ≤ (log x)^c` and all
`a` coprime to `q`. Here `0 ≤ y`; for negative `y` the printed condition fails trivially. -/
def SiegelWalfisz (A : ℕ → Finset ℕ) (δ : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ c →
    ∀ a : ℕ, Nat.Coprime a q → ∀ y : ℝ, 0 ≤ y → y ≤ x →
      |theta (A x) y q a - δ x * y / (Nat.totient q : ℝ)| ≤ C * x / Real.log x ^ (2 * c)

/-- SUPERSEDED, kept for the audit record: hypothesis (3) with the misencoded `thetaReal`;
`LeanLab.PNTPort.PsiChi.xi_siegelWalfisz_false` proves it false for the primes. -/
def SiegelWalfiszReal (A : ℕ → Finset ℕ) (δ : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ c →
    ∀ a : ℕ, Nat.Coprime a q → ∀ y : ℝ, 0 ≤ y → y ≤ x →
      |thetaReal (A x) y q a - δ x * y / (Nat.totient q : ℝ)| ≤ C * x / Real.log x ^ (2 * c)

/-- The relative density bound `δ ≥ (log x)^(-c₀)`, asked for `x ≥ 3`, where `log x > 1`. -/
def DensityFloor (δ : ℕ → ℝ) (c₀ : ℝ) : Prop :=
  ∀ x : ℕ, 3 ≤ x → Real.log x ^ (-c₀) ≤ δ x

/-- `n = p₁ + p₂` with `p₁, p₂ ∈ X`. -/
def IsSumIn (X : Finset ℕ) (n : ℕ) : Prop := ∃ p ∈ X, ∃ q ∈ X, p + q = n

instance (X : Finset ℕ) (n : ℕ) : Decidable (IsSumIn X n) := by
  unfold IsSumIn; infer_instance

/-- The exceptional set `E(x) = {n ≤ x : 2 ∣ n, n ≠ p₁ + p₂, p₁, p₂ ∈ A}`, for positive `n`. -/
def excSet (X : Finset ℕ) (x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter (fun n => Even n ∧ ¬ IsSumIn X n)

/-- The even elements of `(A + A) ∩ [1, x]`. -/
def evenSums (X : Finset ℕ) (x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter (fun n => Even n ∧ IsSumIn X n)

/-- The sumset `A + A`. -/
def sumset (X : Finset ℕ) : Finset ℕ := (X ×ˢ X).image (fun t => t.1 + t.2)

/-! ### Theorem 2 -/

/-- Theorem 2 for a given `c₀ > 0`: if `A ⊆ P ∩ [1, x]` satisfies (3) with
`δ ≥ (log x)^(-c₀)`, then for every `η > 0`, `|E(x)| ≤ C x (log x)^(-η)`. -/
def Theorem2At (c₀ : ℝ) : Prop :=
  ∀ (A : ℕ → Finset ℕ) (δ : ℕ → ℝ), IsPrimeFamily A → DensityFloor δ c₀ → SiegelWalfisz A δ →
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
      ((excSet (A x) x).card : ℝ) ≤ C * x / Real.log x ^ η

/-- Theorem 2: for every `c₀ > 0`. -/
def Theorem2 : Prop := ∀ c₀ : ℝ, 0 < c₀ → Theorem2At c₀

/- Theorem 2 is NOT cited with `sorry`: the paper is WITHDRAWN and Theorem 2 is suspected
false, so asserting it could make the library inconsistent. It stays a `def` only.
Changed by the lead of run 20261017T0402Z-20083. -/

/-! ### Theorem 1 -/

/-- Theorem 1 as printed: `|A + A| = x/2 + O(x (log x)^(-η))`, with the whole sumset.
Not given a cited `sorry`: with `δ = 1` the sumset also holds most evens in `(x, 2x]`,
so the printed form appears false; see the QUESTION in the report. -/
def Theorem1Printed : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ → ∀ (A : ℕ → Finset ℕ) (δ : ℕ → ℝ), IsPrimeFamily A → DensityFloor δ c₀ →
    SiegelWalfisz A δ → ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
      |((sumset (A x)).card : ℝ) - x / 2| ≤ C * x / Real.log x ^ η

/-- Theorem 1 in the form the paper says is equivalent to Theorem 2: the even elements of
`(A + A) ∩ [1, x]` number `⌊x/2⌋ + O(x (log x)^(-η))`. `⌊x/2⌋` is within `1/2` of `x/2`. -/
def Theorem1Even : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ → ∀ (A : ℕ → Finset ℕ) (δ : ℕ → ℝ), IsPrimeFamily A → DensityFloor δ c₀ →
    SiegelWalfisz A δ → ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
      |((evenSums (A x) x).card : ℝ) - ((x / 2 : ℕ) : ℝ)| ≤ C * x / Real.log x ^ η

/- Theorem 1, even form, likewise NOT cited with `sorry`, for the same reason. -/

/-! ## Proved links, zero sorry -/

/-- There are `⌊x/2⌋` even numbers in `[1, x]`. -/
theorem card_even_Icc (x : ℕ) : ((Icc 1 x).filter Even).card = x / 2 := by
  induction x with
  | zero => rfl
  | succ k ih =>
    have h : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
      ext n; simp only [mem_Icc, mem_insert]; omega
    have hn : k + 1 ∉ Icc 1 k := by simp
    rw [h, filter_insert]
    split_ifs with he
    · rw [card_insert_of_notMem (by simp [hn]), ih]
      rcases he with ⟨r, hr⟩; omega
    · rw [ih]
      rw [Nat.not_even_iff_odd] at he; rcases he with ⟨r, hr⟩; omega

/-- `|E(x)| + #{even n ∈ (A + A) ∩ [1, x]} = ⌊x/2⌋`. -/
theorem card_exc_add_card_evenSums (X : Finset ℕ) (x : ℕ) :
    (excSet X x).card + (evenSums X x).card = x / 2 := by
  rw [← card_even_Icc x, ← card_filter_add_card_filter_not (s := (Icc 1 x).filter Even)
    (fun n => IsSumIn X n), filter_filter, filter_filter, excSet, evenSums, add_comm]

/-- The two forms agree: `Theorem1Even ↔ Theorem2`, with the same constants. -/
theorem theorem1Even_iff_theorem2 : Theorem1Even ↔ Theorem2 := by
  have key : ∀ (X : Finset ℕ) (x : ℕ),
      |((evenSums X x).card : ℝ) - ((x / 2 : ℕ) : ℝ)| = ((excSet X x).card : ℝ) := by
    intro X x
    have h := card_exc_add_card_evenSums X x
    have h' : ((x / 2 : ℕ) : ℝ) = (excSet X x).card + (evenSums X x).card := by
      rw [← h]; push_cast; ring
    rw [h', show ((evenSums X x).card : ℝ) - ((excSet X x).card + (evenSums X x).card)
      = -((excSet X x).card : ℝ) by ring, abs_neg, abs_of_nonneg (by positivity)]
  constructor
  · intro h c₀ hc A δ hA hδ hS η hη
    obtain ⟨C, hC⟩ := h c₀ hc A δ hA hδ hS η hη
    exact ⟨C, fun x hx => (key _ _).symm.le.trans (hC x hx)⟩
  · intro h c₀ hc A δ hA hδ hS η hη
    obtain ⟨C, hC⟩ := h c₀ hc A δ hA hδ hS η hη
    exact ⟨C, fun x hx => (key _ _).le.trans (hC x hx)⟩

lemma one_lt_log {x : ℕ} (hx : 3 ≤ x) : 1 < Real.log x := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  have : (3 : ℝ) ≤ x := by exact_mod_cast hx
  linarith [Real.exp_one_lt_d9]

/-- Monotonicity in the density: a smaller `c₀` asks for a larger `δ`, so
Theorem 2 at `c₀'` gives Theorem 2 at every `c₀ ≤ c₀'`. -/
theorem densityFloor_mono {δ : ℕ → ℝ} {c₀ c₀' : ℝ} (h : c₀ ≤ c₀') (hδ : DensityFloor δ c₀) :
    DensityFloor δ c₀' := by
  intro x hx
  refine le_trans ?_ (hδ x hx)
  exact Real.rpow_le_rpow_of_exponent_le (one_lt_log hx).le (by linarith)

theorem theorem2At_mono {c₀ c₀' : ℝ} (h : c₀ ≤ c₀') (h' : Theorem2At c₀') : Theorem2At c₀ :=
  fun A δ hA hδ hS => h' A δ hA (densityFloor_mono h hδ) hS

/-- The case `δ = 1` meets the density floor for every `c₀ > 0`. -/
theorem densityFloor_one {c₀ : ℝ} (hc : 0 < c₀) : DensityFloor (fun _ => 1) c₀ := by
  intro x hx
  exact Real.rpow_le_one_of_one_le_of_nonpos (one_lt_log hx).le (by linarith)

/-! ### The classical case `A = P ∩ [1, x]` -/

/-- `P ∩ [1, x]`. -/
def primesUpTo (x : ℕ) : Finset ℕ := (Icc 1 x).filter Nat.Prime

theorem primesUpTo_family : IsPrimeFamily primesUpTo := by
  intro x p hp
  simp only [primesUpTo, mem_filter, mem_Icc] at hp
  exact ⟨hp.2, hp.1.2⟩

/-- For `n ≤ x`, being a sum of two primes in `[1, x]` is being a Goldbach sum. -/
theorem isSumIn_primesUpTo_iff {x n : ℕ} (hn : n ≤ x) :
    IsSumIn (primesUpTo x) n ↔ IsGoldbachSum n := by
  constructor
  · rintro ⟨p, hp, q, hq, h⟩
    simp only [primesUpTo, mem_filter] at hp hq
    exact ⟨p, q, hp.2, hq.2, h⟩
  · rintro ⟨p, q, hp, hq, h⟩
    refine ⟨p, ?_, q, ?_, h⟩ <;> simp only [primesUpTo, mem_filter, mem_Icc]
    · exact ⟨⟨hp.one_lt.le, by omega⟩, hp⟩
    · exact ⟨⟨hq.one_lt.le, by omega⟩, hq⟩

/-- Even `n ∈ [1, x]` that are not Goldbach sums. This is the classical exceptional set
plus the number `2`. -/
noncomputable def classicalExc (x : ℕ) : ℕ := by
  classical
  exact ((Icc 1 x).filter (fun n => Even n ∧ ¬ IsGoldbachSum n)).card

theorem excSet_primesUpTo (x : ℕ) : (excSet (primesUpTo x) x).card = classicalExc x := by
  classical
  unfold classicalExc excSet
  congr 1
  apply filter_congr
  intro n hn
  rw [mem_Icc] at hn
  rw [isSumIn_primesUpTo_iff hn.2]

/-- The classical log power saving for the exceptional set of binary Goldbach. -/
def ClassicalLogSaving : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x → (classicalExc x : ℝ) ≤ C * x / Real.log x ^ η

/-- The paper's remark that Theorem 2 contains the classical result with `δ = 1`, as an
implication: Theorem 2 at any `c₀ > 0`, plus hypothesis (3) for all primes with `δ = 1`,
which is the Siegel-Walfisz theorem and is NOT proved here, gives the classical bound. -/
theorem classical_of_theorem2 {c₀ : ℝ} (hc : 0 < c₀) (h : Theorem2At c₀)
    (hSW : SiegelWalfisz primesUpTo (fun _ => 1)) : ClassicalLogSaving := by
  intro η hη
  obtain ⟨C, hC⟩ := h primesUpTo _ primesUpTo_family (densityFloor_one hc) hSW η hη
  exact ⟨C, fun x hx => by rw [← excSet_primesUpTo]; exact hC x hx⟩

/-! ### Kernel examples -/

/-- With `A = P ∩ [1, 100]`, `E(100) = {2}`. -/
theorem excSet_primes_100 : excSet (primesUpTo 100) 100 = {2} := by decide

theorem excSet_primes_100_card : (excSet (primesUpTo 100) 100).card = 1 := by
  rw [excSet_primes_100]; rfl

/-! ### The elementary obstruction behind the WARNING -/

/-- If `{a α} < 1/4` and `{b α} < 1/4` then `{(a + b) α} < 1/2`. -/
theorem fract_sum_lt_half (α : ℝ) {a b : ℕ} (ha : Int.fract ((a : ℝ) * α) < 1 / 4)
    (hb : Int.fract ((b : ℝ) * α) < 1 / 4) : Int.fract (((a + b : ℕ) : ℝ) * α) < 1 / 2 := by
  have h := Int.fract_add_le ((a : ℝ) * α) ((b : ℝ) * α)
  push_cast; rw [add_mul]; linarith

open Classical in
/-- If every `p ∈ X` has `{p α} < 1/4`, every even `n ∈ [1, x]` with `{n α} ≥ 1/2` lies in
the exceptional set `E(x)` of `X`. -/
theorem excSet_of_fract (X : Finset ℕ) (x : ℕ) (α : ℝ)
    (hX : ∀ p ∈ X, Int.fract ((p : ℝ) * α) < 1 / 4) :
    (Icc 1 x).filter (fun n : ℕ => Even n ∧ 1 / 2 ≤ Int.fract ((n : ℝ) * α)) ⊆ excSet X x := by
  intro n hn
  simp only [mem_filter] at hn
  simp only [excSet, mem_filter]
  refine ⟨hn.1, hn.2.1, ?_⟩
  rintro ⟨p, hp, q, hq, rfl⟩
  have := fract_sum_lt_half α (hX p hp) (hX q hq)
  linarith [hn.2.2]

end LeanLab.Xi2012
