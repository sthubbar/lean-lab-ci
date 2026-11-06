import LeanLab.GoldbachAverage.Decomp287c
import Mathlib.Data.Nat.Factorization.Basic

/-!
Bhowmik and Schlage Puchta, arXiv 0806.3295v3 page 5, the pair averaging displays.
The residue product and the antidiagonal reindexing are separate finite leaves.
The number of admissible multiples and the final pigeonhole step are proved here.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp402b
open Finset
open Decomp287c
open scoped ArithmeticFunction.vonMangoldt

/-- The multiples in the pair window from the averaging display on BSP page 5. -/
def pairWindow (x q : ℕ) : Finset ℕ :=
  (Ioc (2 * x) (4 * x)).filter (fun n => q ∣ n)

/-- The complementary reduced residue products in the first averaging display on BSP page 5. -/
def residuePairMass (x q : ℕ) : ℝ :=
  ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    progressionMass x q a * progressionMass x q ((q - a) % q)

/-- The count of multiples is bounded by the full positive interval, BSP page 5 final display. -/
theorem pairWindow_card (x q : ℕ) : (pairWindow x q).card ≤ 4 * x / q := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  apply card_le_card
  intro n hn
  obtain ⟨hn, hd⟩ := mem_filter.mp hn
  have hb := mem_Ioc.mp hn
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, hb.2⟩, hd⟩

/-- BSP page 5 final display, with the cardinal bound written over the reals. -/
theorem pairWindow_card_real (x q : ℕ) (hq : 0 < q) :
    ((pairWindow x q).card : ℝ) ≤ 4 * (x : ℝ) / q := by
  have hmul : (pairWindow x q).card * q ≤ 4 * x :=
    (Nat.mul_le_mul_right q (pairWindow_card x q)).trans (Nat.div_mul_le_self _ _)
  apply (le_div_iff₀ (by exact_mod_cast hq : (0 : ℝ) < q)).mpr
  exact_mod_cast hmul

/-- LEAF. BSP page 5, the lower bound in the first pair averaging display.
There are phi q reduced classes and each complementary window mass has the stated lower bound.
This assertion only multiplies and sums the progression hypotheses. -/
theorem residue_pair_lower (x q : ℕ) (hx : 2 ≤ x) (hq : 0 < q)
    (hAP : ∀ a : ℕ, a < q → Nat.Coprime a q →
      (x : ℝ) / (2 * Nat.totient q) ≤ progressionMass x q a) :
    (x : ℝ) ^ 2 / (4 * Nat.totient q) ≤ residuePairMass x q := by
  have ht : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  let S := (range q).filter (fun a => Nat.Coprime a q)
  have hc : S.card = Nat.totient q := by
    simp only [S, Nat.totient_eq_card_coprime, Nat.coprime_comm]
  have hp : ∀ a ∈ S, ((x : ℝ) / (2 * Nat.totient q)) ^ 2 ≤
      progressionMass x q a * progressionMass x q ((q - a) % q) := by
    intro a ha
    obtain ⟨haq, hac⟩ := mem_filter.mp ha
    have hal : a < q := mem_range.mp haq
    have hcomp : Nat.Coprime ((q - a) % q) q := by
      rw [ZMod.coprime_mod_iff_coprime]
      exact (Nat.coprime_self_sub_left hal.le).mpr hac
    have h1 := hAP a hal hac
    have h2 := hAP ((q - a) % q) (Nat.mod_lt _ hq) hcomp
    calc ((x : ℝ) / (2 * Nat.totient q)) ^ 2 =
        ((x : ℝ) / (2 * Nat.totient q)) * ((x : ℝ) / (2 * Nat.totient q)) := by ring
      _ ≤ progressionMass x q a * progressionMass x q ((q - a) % q) :=
        mul_le_mul h1 h2 (by positivity) (le_trans (by positivity) h1)
  have hs := sum_le_sum hp
  rw [sum_const, nsmul_eq_mul, hc] at hs
  have he : (Nat.totient q : ℝ) * ((x : ℝ) / (2 * Nat.totient q)) ^ 2 =
      (x : ℝ) ^ 2 / (4 * Nat.totient q) := by field_simp [ht.ne']; ring
  rw [he] at hs
  exact hs

/-- LEAF. BSP page 5, the upper bound for the residue product in the pair averaging display.
Reindex each pair of window indices by its sum in the antidiagonal defining G.
Complementary classes force divisibility by q and both endpoints force the pair window.
No progression lower bound is assumed in this finite counting assertion. -/
theorem residue_pair_le_convolution (x q : ℕ) (hq : 0 < q) :
    residuePairMass x q ≤ ∑ n ∈ pairWindow x q, G n := by
  classical
  let S := (range q).filter (fun a => Nat.Coprime a q)
  let W := fun a => (Ioc x (2 * x)).filter (fun n => n % q = a)
  let src := S.sigma (fun a => (W a).product (W ((q - a) % q)))
  let dst := (pairWindow x q).sigma (fun n => antidiagonal n)
  let e : (Σ _ : ℕ, ℕ × ℕ) → (Σ _ : ℕ, ℕ × ℕ) :=
    fun z => ⟨z.2.1 + z.2.2, z.2⟩
  have hr (z : Σ _ : ℕ, ℕ × ℕ) (hz : z ∈ src) : z.2.1 % q = z.1 := by
    have hp := (mem_sigma.mp hz).2
    exact (mem_filter.mp (mem_product.mp hp).1).2
  have hinj : Set.InjOn e src := by
    intro z hz w hw he
    have hp : z.2 = w.2 := by
      simpa only [e] using (congrArg (fun t : Σ _ : ℕ, ℕ × ℕ => t.2) he)
    have ha : z.1 = w.1 := by rw [← hr z hz, ← hr w hw, hp]
    exact Sigma.ext ha (heq_of_eq hp)
  have hmap (z : Σ _ : ℕ, ℕ × ℕ) (hz : z ∈ src) : e z ∈ dst := by
    obtain ⟨hs, hp⟩ := mem_sigma.mp hz
    obtain ⟨hn, hm⟩ := mem_product.mp hp
    obtain ⟨hnw, hnr⟩ := mem_filter.mp hn
    obtain ⟨hmw, hmr⟩ := mem_filter.mp hm
    have hal : z.1 < q := mem_range.mp (mem_filter.mp hs).1
    have hnwin := mem_Ioc.mp hnw
    have hmwin := mem_Ioc.mp hmw
    have hdiv : q ∣ z.2.1 + z.2.2 := by
      apply Nat.dvd_of_mod_eq_zero
      calc (z.2.1 + z.2.2) % q = (z.2.1 % q + z.2.2 % q) % q := Nat.add_mod _ _ _
        _ = (z.1 + (q - z.1) % q) % q := by rw [hnr, hmr]
        _ = (z.1 + (q - z.1)) % q := by
          rw [Nat.add_mod z.1 (q - z.1) q, Nat.mod_eq_of_lt hal]
        _ = 0 := by rw [Nat.add_sub_of_le hal.le, Nat.mod_self]
    apply mem_sigma.mpr
    constructor
    · apply mem_filter.mpr
      exact ⟨mem_Ioc.mpr ⟨by dsimp [e]; omega, by dsimp [e]; omega⟩, hdiv⟩
    · exact mem_antidiagonal.mpr rfl
  have hs : (∑ z ∈ src, (Λ z.2.1 : ℝ) * Λ z.2.2) ≤
      ∑ z ∈ dst, (Λ z.2.1 : ℝ) * Λ z.2.2 := by
    apply sum_le_sum_of_injOn e hinj
    · intro j hj
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hj
      exact hmap z hz
    · intro z _
      exact le_rfl
    · intro z _ _
      exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
  have hsrc : residuePairMass x q = ∑ z ∈ src, (Λ z.2.1 : ℝ) * Λ z.2.2 := by
    simp only [residuePairMass, src, S, W, sum_sigma,
      progressionMass]
    apply sum_congr rfl
    intro a ha
    simp only [Finset.product_eq_sprod]
    rw [sum_product]
    rw [sum_mul]
    apply sum_congr rfl
    intro n hn
    rw [mul_sum]
  have hdst : (∑ z ∈ dst, (Λ z.2.1 : ℝ) * Λ z.2.2) = ∑ n ∈ pairWindow x q, G n := by
    simp only [dst, sum_sigma, G]
  rw [← hsrc, hdst] at hs
  exact hs

/-- The exact progression_pair_average target follows from the two finite leaves.
CONDITIONAL ON the displayed progression lower bounds. -/
theorem progression_pair_average_assembled (x q : ℕ) (hx : 2 ≤ x) (hq : 0 < q) (hqx : q ≤ x)
    (hAP : ∀ a : ℕ, a < q → Nat.Coprime a q →
      (x : ℝ) / (2 * Nat.totient q) ≤ progressionMass x q a) :
    ∃ N : ℕ, 2 * x < N ∧ N ≤ 4 * x ∧
      (x : ℝ) * q / (16 * Nat.totient q) ≤ G N := by
  have ht : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hlow := (residue_pair_lower x q hx hq hAP).trans (residue_pair_le_convolution x q hq)
  have hne : (pairWindow x q).Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty.mp hn, sum_empty] at hlow
    have hp : (0 : ℝ) < (x : ℝ) ^ 2 / (4 * Nat.totient q) := by positivity
    linarith
  have hex : ∃ N ∈ pairWindow x q, (x : ℝ) * q / (16 * Nat.totient q) ≤ G N := by
    by_contra! hn
    obtain ⟨n, hnmem⟩ := hne
    have hs := sum_lt_sum (fun n hnmem => (hn n hnmem).le)
      ⟨n, hnmem, hn n hnmem⟩
    rw [sum_const, nsmul_eq_mul] at hs
    have hc := mul_le_mul_of_nonneg_right (pairWindow_card_real x q hq)
      (show 0 ≤ (x : ℝ) * q / (16 * Nat.totient q) by positivity)
    have he : (4 * (x : ℝ) / q) * ((x : ℝ) * q / (16 * Nat.totient q)) =
        (x : ℝ) ^ 2 / (4 * Nat.totient q) := by field_simp [hq0.ne', ht.ne']; ring
    rw [he] at hc
    linarith
  obtain ⟨N, hN, hGN⟩ := hex
  have hwin := mem_Ioc.mp (mem_filter.mp hN).1
  exact ⟨N, hwin.1, hwin.2, hGN⟩

example : type_of% progression_pair_average = type_of% progression_pair_average_assembled := rfl

end LeanLab.GoldbachAverage.Decomp402b
