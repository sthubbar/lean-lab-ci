import LeanLab.Linnik.Decomp466a

namespace LeanLab.Linnik.Decomp1532c

open LeanLab.Linnik.Decomp482a
open LeanLab.Linnik.U7204

lemma near_attempt (θ : ℝ) (hθ : 0 < θ) (hθ4 : θ ≤ 1 / 4)
    (k : ℕ) (hk : 2 ≤ k) (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hN : 2 ≤ N)
    (x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N))
    (hx : (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|) :
    complexFrequencyError N θ (LeanLab.Linnik.Decomp1532a.dif x) ≤
      (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 9) := by
  obtain ⟨c, K, θ₀, hc, hK, hθ₀, hθ₀1, hfreq⟩ :=
    LeanLab.Linnik.Decomp466a.gallagher_theorem3
  obtain ⟨r, hr, hper⟩ := hfreq θ hθ hθ4 N hN
  have h := hper (LeanLab.Linnik.Decomp1532a.dif x) (by
    intro hz
    exact hz (by simpa using hx))
  exact h

end LeanLab.Linnik.Decomp1532c
