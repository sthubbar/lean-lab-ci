/-
P0045, journal pages 777 to 779, displays 20 to 24 and 28 to 30.
The actual count tail follows from the proved Romanov series and the product remainder estimate.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LPZ2007.D4SingleBound
import LeanLab.LPZ2007.D4Recursion

namespace LeanLab.LPZ2007.D4TailProof

open Finset Filter Topology Real
open LeanLab.LPZ2007 LeanLab.LPZ2007.Eq14FromCor42 LeanLab.LPZ2007.D4Tail
open LeanLab.LPZ2007.D4Asymptotic LeanLab.LPZ2007.D4Recursion
open LeanLab.LPZ2007.D4SingleBound LeanLab.LPZ2007.R3FromS3

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The actual large-period count tail is uniformly small. -/
theorem uniformD4Tail_proved : (∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ T0 : ℕ, ∀ T : ℕ, T0 ≤ T →
    ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ N : ℕ, Even N → InJ X N →
      ∑ d ∈ (Icc 1 N).filter (fun d => OddSqf d ∧ T < xi d),
        fd d * (#{ν ∈ tuples k ⌊Lp X⌋₊ | d ∣ N - pow2sum ν} : ℝ) ≤ ε * Lg X ^ k) := by
  intro k hk ε hε
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  let δ := ε / 2
  have hδ : 0 < δ := by positivity
  obtain ⟨T0, hT0⟩ := ((tendsto_order.1 (tendsto_sum_nat_add romanovTerm)).2 δ hδ).exists_forall_of_atTop
  refine ⟨T0, fun T hT => ?_⟩
  let L0 : ℝ := 36 * ((j + 1 : ℕ) : ℝ) ^ 2 + (6 * exp 27 / δ) ^ 2 + 2
  refine ⟨max 2 ((2 : ℝ) ^ L0), fun X hX N _hNe hNJ => ?_⟩
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := by linarith
  have hLL : L0 ≤ Lg X := Lg_ge ((le_max_right _ _).trans hX)
  let L := Lg X
  let M := ⌊Lp X⌋₊
  have hL36 : 36 * ((j + 1 : ℕ) : ℝ) ^ 2 ≤ L := by
    dsimp [L0] at hLL
    dsimp [L]
    nlinarith [sq_nonneg (6 * exp 27 / δ)]
  have hLδ : (6 * exp 27 / δ) ^ 2 + 1 ≤ L := by
    dsimp [L0] at hLL
    dsimp [L]
    nlinarith [sq_nonneg (((j + 1 : ℕ) : ℝ))]
  have hL1 : 1 ≤ L := by nlinarith [sq_nonneg (6 * exp 27 / δ)]
  have hM : (M : ℝ) ≤ L := by
    have hs : √L ≤ L := (Real.sqrt_le_left (by linarith)).2 (by nlinarith)
    have hLp : 0 ≤ Lp X := by change 0 ≤ L - √L; linarith
    have hfloor : (M : ℝ) ≤ L - √L := Nat.floor_le hLp
    linarith [Real.sqrt_nonneg L]
  let F := (Icc 1 N).filter (fun d => OddSqf d ∧ T < xi d)
  have hF : ∀ d ∈ F, OddSqf d := fun d hd => (mem_filter.1 hd).2.1
  have hFd : ∀ d ∈ F, T < d := by
    intro d hd
    have hξ := (mem_filter.1 hd).2.2
    have hxd := (Lemma61Port.xi_spec_sqf (hF d hd)).2.1
    omega
  have hcoeff : ∑ d ∈ F, romanovTerm d ≤ δ := by
    have hs : Summable (fun n => romanovTerm (n + (T + 1))) :=
      (summable_nat_add_iff (T + 1)).2 Lemma61Port.lemma61_proved
    have he : ∑ d ∈ F, romanovTerm d =
        ∑ n ∈ F.image (fun d => d - (T + 1)), romanovTerm (n + (T + 1)) := by
      rw [sum_image]
      · apply sum_congr rfl
        intro d hd
        have := hFd d hd
        congr 1
        omega
      · intro a ha b hb hab
        have := hFd a ha
        have := hFd b hb
        change a - (T + 1) = b - (T + 1) at hab
        omega
    rw [he]
    exact (hs.sum_le_tsum _ (fun n _ => Lemma61Port.romanovTerm_nonneg _)).trans
      (hT0 (T + 1) (by omega)).le
  have hlog : log X = L * log 2 := by
    dsimp [L, Lg, Real.logb]
    field_simp
  have hsmall : ∀ ν ∈ tuples (j + 1) M, pow2sum ν < N := by
    intro ν hν
    have h1 := pow2sum_small hk hX0 hL36 hν
    exact_mod_cast (show (pow2sum ν : ℝ) < N by linarith [hNJ.1])
  have hsingle : ∀ t ∈ tuples j M,
      ∑ d ∈ F, fd d * (oneCount d M (N - pow2sum t) : ℝ) ≤ ε * L := by
    intro t ht
    have hpow : ∀ a ∈ Icc 1 M, 2 ^ a < N - pow2sum t := by
      intro a ha
      have hcons : (Fin.cons a t : Fin (j + 1) → ℕ) ∈ tuples (j + 1) M := by
        simp only [tuples, Fintype.mem_piFinset] at ht ⊢
        intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · simpa using ha
        · simpa using ht i
      have hp := hsmall _ hcons
      rw [pow2sum_cons] at hp
      omega
    have hmX : ((N - pow2sum t : ℕ) : ℝ) ≤ X :=
      (show ((N - pow2sum t : ℕ) : ℝ) ≤ N by exact_mod_cast Nat.sub_le N _).trans hNJ.2
    have h := weighted_one_small F M (N - pow2sum t) hF hpow hX0 hδ hlog hmX hM hcoeff hLδ
    dsimp [δ] at h
    linarith
  change ∑ d ∈ F, fd d *
    (#{ν ∈ tuples (j + 1) M | d ∣ N - pow2sum ν} : ℝ) ≤ ε * L ^ (j + 1)
  simp_rw [count_succ_eq, mul_sum]
  rw [sum_comm]
  calc ∑ t ∈ tuples j M, ∑ d ∈ F, fd d * (oneCount d M (N - pow2sum t) : ℝ)
      ≤ ∑ _t ∈ tuples j M, ε * L := sum_le_sum hsingle
    _ = (M : ℝ) ^ j * (ε * L) := by rw [sum_const, nsmul_eq_mul, card_tuples, Nat.cast_pow]
    _ ≤ L ^ j * (ε * L) := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hM _) (by positivity)
    _ = ε * L ^ (j + 1) := by rw [pow_succ]; ring

end
end LeanLab.LPZ2007.D4TailProof

#print axioms LeanLab.LPZ2007.D4TailProof.uniformD4Tail_proved
