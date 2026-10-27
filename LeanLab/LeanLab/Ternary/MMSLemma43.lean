/-
P0028, arXiv 1610.02017, Lemma 4.3 on pages 8 and 9.
The statement uses full integer transforms after smoothing.
The global existence statement remains an unproved Prop.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSBohrBounds
import LeanLab.Ternary.MMSProp31

namespace LeanLab.Ternary.MMS

/-- The four conclusions of Lemma 4.3, with f extended by zero on the integers. -/
def Lemma43Data (N : ℕ) (η ε K q δ C : ℝ) (f : ℕ → ℝ) (g h : ℤ →₀ ℝ) : Prop :=
  intervalLift N f = g + h ∧
  (∀ n : ℤ, 0 ≤ g n ∧ g n ≤ 1 + C * η) ∧
  (∀ γ : ℝ, ‖intHat h γ‖ ≤ δ * N) ∧
  DenseOnAPs N (η + δ / ε) (ε / 2) (fun n => g n) ∧
  intLq g q ≤ K * (N : ℝ) ^ (1 - 1 / q) ∧
  intLq h q ≤ K * (N : ℝ) ^ (1 - 1 / q)

/-- P0028 Lemma 4.3. The big O bound has an explicit constant.
The constant depends on the fixed ε, K, q and δ. No proof is supplied here. -/
def Lemma43 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ K q : ℝ, 1 ≤ K → 2 < q → q < 3 →
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C ≥ (0 : ℝ),
    ∀ η : ℝ, 0 < η → η < 1 → ∀ (N : ℕ), 1 ≤ N → ∀ f : ℕ → ℝ,
      Prop31Hyp N η ε K q f → ∃ g h : ℤ →₀ ℝ, Lemma43Data N η ε K q δ C f g h

/-- A nonempty concrete instance of all the hypotheses and conclusions.
Take N = 1, f = 1, g its extension by zero, h = 0 and C = 0. -/
theorem lemma43_one_instance :
    ∃ K : ℝ, 1 ≤ K ∧ Prop31Hyp 1 (1 / 2) (1 / 6) K (5 / 2) (fun _ => 1) ∧
      Lemma43Data 1 (1 / 2) (1 / 6) K (5 / 2) (1 / 2) 0 (fun _ => 1)
        (intervalLift 1 (fun _ => 1)) 0 := by
  obtain ⟨K, hK, h⟩ := prop31Hyp_one 1 le_rfl
  have hf := h (1 / 2) (by norm_num)
  refine ⟨K, hK, hf, ?_⟩
  have hg : intervalLift 1 (fun _ => (1 : ℝ)) = Finsupp.single (1 : ℤ) 1 := by
    simp [intervalLift]
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [hg]
    by_cases hn : n = 1 <;> simp [Finsupp.single_apply, hn, eq_comm]
  · intro γ
    simp [intHat]
  · intro P hP hlen
    have havg : avg (fun n => intervalLift 1 (fun _ => (1 : ℝ)) n) P = 1 := by
      calc avg (fun n => intervalLift 1 (fun _ => (1 : ℝ)) n) P =
          avg (fun _ => (1 : ℝ)) P := by
            unfold avg
            congr 1
            apply Finset.sum_congr rfl
            intro n hn
            obtain ⟨a, d, L, hd, hL, hEq, hIn⟩ := hP
            have hnp := hIn n hn
            have hn1 : n = 1 := by omega
            subst n
            simp [hg]
        _ = 1 := avg_one hP.card_pos
    rw [havg]
    norm_num
  · rw [intLq_intervalLift]
    exact hf.2.2.2
  · norm_num [intLq, intHat]
    linarith

end LeanLab.Ternary.MMS
