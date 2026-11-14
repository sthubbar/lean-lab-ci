import LeanLab.ExceptionalSet.State1539Data264
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
Derived affine modulation helpers for P0082 pages370 and371.
The last theorem is CONDITIONAL ON Lemma10.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.AffinePhase553
open LeanLab.ExceptionalSet.U1539

/-- P0082 pages370 and371, derived higher derivative invariance for completion. -/
theorem iteratedDeriv_add_affine (f : ℝ → ℝ) (n : ℕ) (x a b : ℝ)
    (hf : ContDiffAt ℝ n f x) (hn : 2 ≤ n) :
    iteratedDeriv n (fun y => f y + a * y + b) x = iteratedDeriv n f x := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have haff : iteratedDeriv n (fun y : ℝ => a * y + b) x = 0 := by
    rw [iteratedDeriv_fun_add (by fun_prop) (by fun_prop), iteratedDeriv_const_mul_field]
    simp [iteratedDeriv_fun_id, iteratedDeriv_const, hn0, hn1]
  have he : (fun y => f y + a * y + b) = (fun y => f y + (a * y + b)) := by
    funext y
    ring
  rw [he, iteratedDeriv_fun_add hf (by fun_prop), haff, add_zero]

/-- P0082 page370 Lemma10, derived affine modulation stability.
Erasing derivative order one spends at most half the derivative budget. -/
theorem KClass_add_affine (N k : ℕ) (θ Θ Θ₀ δ : ℝ) (f : ℝ → ℝ)
    (a b : ℝ) (hK : KClass N θ Θ Θ₀ δ f k) (hbudget : 2 ≤ δ * k) :
    KClass N θ Θ Θ₀ (δ / 2) (fun x => f x + a * x + b) k := by
  unfold KClass at hK ⊢
  rcases hK with ⟨hk, ⟨U, hU, hIU, hf⟩, hD, S, hS, hcard, hDS⟩
  refine ⟨hk, ⟨U, hU, hIU, ?_⟩, ?_, S.erase 1, (Finset.erase_subset _ _).trans hS, ?_, ?_⟩
  · have hlin : ContDiffOn ℝ k (fun x : ℝ => a * x + b) U := by fun_prop
    convert hf.add hlin using 1
    funext x
    ring
  · intro x hx
    rw [iteratedDeriv_add_affine f k x a b (hf.contDiffAt (hU.mem_nhds (hIU hx))) (by omega)]
    exact hD x hx
  · have hcNat : S.card ≤ (S.erase 1).card + 1 := by
      by_cases h1 : 1 ∈ S
      · exact (Finset.card_erase_add_one h1).symm.le
      · simp [h1]
    have hcR : (S.card : ℝ) ≤ ((S.erase 1).card : ℝ) + 1 := by exact_mod_cast hcNat
    nlinarith
  · intro s hs x hx
    have hsS : s ∈ S := (Finset.mem_erase.mp hs).2
    have hs1 : s ≠ 1 := (Finset.mem_erase.mp hs).1
    have hsI := Finset.mem_Icc.mp (hS hsS)
    have hs2 : 2 ≤ s := by omega
    have hsk : s ≤ k := by omega
    have hAt : ContDiffAt ℝ s f x :=
      (hf.contDiffAt (hU.mem_nhds (hIU hx))).of_le (by exact_mod_cast hsk)
    rw [iteratedDeriv_add_affine f s x a b hAt hs2]
    exact hDS s hsS x hx

/-- P0082 page370 Lemma10, affine completion input from its cited bound.
CONDITIONAL ON the explicit Karacuba hypothesis h10. -/
theorem bound_affine_twist_of_lemma10 (h10 : Lemma10) (θ Θ Θ₀ δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hΘ : 0 < Θ) (hΘθ : Θ < θ)
    (hθΘ₀ : θ < Θ₀) (hΘ₀ : Θ₀ < 1) :
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ N : ℕ, 1 ≤ N →
      ∀ (f : ℝ → ℝ) (k : ℕ), KClass N θ Θ Θ₀ δ f k → 2 ≤ δ * k →
        ∀ a b : ℝ,
          ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n + a * n + b)‖ ≤
            B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  obtain ⟨B, c, hB, hc, hb⟩ := h10 θ Θ Θ₀ (δ / 2) (by positivity) (by linarith)
    hΘ hΘθ hθΘ₀ hΘ₀
  refine ⟨B, c, hB, hc, fun N hN f k hK hbudget a b => ?_⟩
  exact hb N hN (fun x => f x + a * x + b) k (KClass_add_affine N k θ Θ Θ₀ δ f a b hK hbudget)

end LeanLab.ExceptionalSet.AffinePhase553
