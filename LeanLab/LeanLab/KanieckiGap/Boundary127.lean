/-
P0022, page 371. Two certified boundary primes close the endpoint difference
between the two Young-Potler inputs. These are helper certificates.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Verifications.Pratt
import LeanLab.KanieckiGap.Decomp127

namespace LeanLab.KanieckiGap.Boundary127

open LeanLab.Verifications.Pratt

/-- Page 371, boundary conversion certificate. The prime 13084789 supports the endpoint check. -/
theorem prime_13084789 : Nat.Prime 13084789 := by
  refine pratt 13084789 6 [(2, 2), (3, 1), (283, 1), (3853, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

/-- Page 371, boundary conversion certificate. The prime 38469279661 supports the endpoint check. -/
theorem prime_38469279661 : Nat.Prime 38469279661 := by
  refine pratt 38469279661 2 [(2, 2), (3, 1), (5, 1), (7, 2), (13084789, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact prime_13084789

/-- Page 371, boundary conversion certificate. The prime 72629999999969 supports the endpoint check. -/
theorem prime_72629999999969 : Nat.Prime 72629999999969 := by
  refine pratt 72629999999969 6 [(2, 5), (59, 1), (38469279661, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact prime_38469279661

/-- Page 371, boundary conversion certificate. The prime 850139 supports the endpoint check. -/
theorem prime_850139 : Nat.Prime 850139 := by
  refine pratt 850139 2 [(2, 1), (127, 1), (3347, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

/-- Page 371, boundary conversion certificate. The prime 91243718593 supports the endpoint check. -/
theorem prime_91243718593 : Nat.Prime 91243718593 := by
  refine pratt 91243718593 5 [(2, 6), (3, 1), (13, 1), (43, 1), (850139, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact prime_850139

/-- Page 371, boundary conversion certificate. The prime 72630000000029 supports the endpoint check. -/
theorem prime_72630000000029 : Nat.Prime 72630000000029 := by
  refine pratt 72630000000029 2 [(2, 2), (199, 1), (91243718593, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact prime_91243718593

end LeanLab.KanieckiGap.Boundary127

#print axioms LeanLab.KanieckiGap.Boundary127.prime_13084789
#print axioms LeanLab.KanieckiGap.Boundary127.prime_38469279661
#print axioms LeanLab.KanieckiGap.Boundary127.prime_72629999999969
#print axioms LeanLab.KanieckiGap.Boundary127.prime_850139
#print axioms LeanLab.KanieckiGap.Boundary127.prime_91243718593
#print axioms LeanLab.KanieckiGap.Boundary127.prime_72630000000029
