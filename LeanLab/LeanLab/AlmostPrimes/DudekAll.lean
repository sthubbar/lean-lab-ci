import LeanLab.AlmostPrimes.DudekFrom1e9
import LeanLab.Verifications.Top50.BitUpTo1e9
import LeanLab.AlmostPrimes.BJSThm5NoDusart

/-!
# Dudek's prime plus square-free theorem for every even `N ≥ 4`, no cited input

Unit U-5662, CLOUD 20261019T1515Z-cloud27, I-5067. AI wrote the Lean code. KNOWN mathematics,
Dudek 2017, BJS Theorem 53. `DudekFrom1e9.dudek_even_of_1e9` with the lab's kernel-checked
`Verifications.Top50.Bits.evenGoldbachUpTo_1e9`. Goldbach itself is OPEN.
-/

namespace LeanLab.AlmostPrimes.DudekAll

/-- **Every even `N ≥ 4` is a prime plus a positive square-free number. PROVED, no cited input.** -/
theorem dudek_even (N : ℕ) (hE : Even N) (h4 : 4 ≤ N) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m :=
  LeanLab.AlmostPrimes.DudekFrom1e9.dudek_even_of_1e9
    LeanLab.Verifications.Top50.Bits.evenGoldbachUpTo_1e9 N hE h4

/-- `DudekLarge.DudekEvenBelow`, the finite input of `bjs_thm5_of_3273_small`, PROVED. -/
theorem dudekEvenBelow : LeanLab.AlmostPrimes.DudekLarge.DudekEvenBelow :=
  fun N hE h4 _ => dudek_even N hE h4

open LeanLab.AlmostPrimes in
/-- **BJS Theorem 5 at `e^29.4`, CONDITIONAL ON the Chen form at `exp(exp 32.73)` only.** Every even
`N ≥ 4` is `p + m` with `Ω(m) ≤ e^29.4`; Dudek, both Dusart bounds and the `4·10¹⁸` check are gone. -/
theorem bjs_thm5_294_chen
    (h3273 : ∀ N : ℕ, Even N → Real.exp (Real.exp 32.73) < N → PrimePlusAlmostPrime 2 N) :
    ∀ N : ℕ, Even N → 4 ≤ N → ∃ k : ℕ, (k : ℝ) ≤ Real.exp 29.4 ∧ PrimePlusAlmostPrime k N := by
  intro N hE hN
  by_cases hbig : Real.exp (Real.exp 32.73) < N
  · refine ⟨2, ?_, h3273 N hE hbig⟩
    have := Real.add_one_le_exp 29.4
    push_cast; linarith
  · push Not at hbig
    obtain ⟨p, m, hp, hm, hsq, hNpm⟩ := dudek_even N hE hN
    refine ⟨ArithmeticFunction.cardFactors m, ?_, ⟨p, m, hp, hm, hNpm, le_rfl⟩⟩
    apply NoDusart.omega_le_of_log hm hsq
    have hmN : (m : ℝ) ≤ N := by exact_mod_cast (by omega : m ≤ N)
    calc Real.log m ≤ Real.log (Real.exp (Real.exp 32.73)) :=
          Real.log_le_log (by exact_mod_cast hm) (hmN.trans hbig)
      _ = Real.exp 32.73 := Real.log_exp _

end LeanLab.AlmostPrimes.DudekAll
