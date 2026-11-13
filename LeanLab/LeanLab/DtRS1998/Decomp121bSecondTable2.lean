/-
AI wrote this Lean code for route burst session 9, 2026-11-12, target second_family.
P0037 Table 2, printed page 214. Consistency checks of the printed data with the
definition of W on page 214: W - q_i is composite for i = 1, ..., Nq - 1 and prime
for i = Nq. Only q1 = B - (B - q1), q_Nq = B + (q_Nq - B) and W = B + (W - B) are
printed; the full prime lists q1, ..., q_Nq are not printed, so the certificate
leaves table2_certificates_lower and table2_certificates_upper stay OPEN.
These lemmas do not discharge those leaves. Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.DtRS1998.Decomp121bSecondTable2

set_option exponentiation.threshold 400

/-- P0037 Table 2 page 214, row log10 B = 200: W - B = 999786382, q_Nq - B = 999497853.
The definition of W on page 214 says W - q_Nq is prime. PROVED. -/
theorem row200_W_sub_qN_prime :
    (10 ^ 200 + 999786382 - (10 ^ 200 + 999497853) : ℕ).Prime := by
  rw [show (10 ^ 200 + 999786382 - (10 ^ 200 + 999497853) : ℕ) = 288529 by norm_num]
  norm_num

/-- P0037 Table 2 page 214, row log10 B = 200: B - q1 = 97283.
The definition of W on page 214 says W - q1 is composite; here W - q1 = 999883665,
divisible by 3. PROVED. -/
theorem row200_W_sub_q1_not_prime :
    ¬ (10 ^ 200 + 999786382 - (10 ^ 200 - 97283) : ℕ).Prime := by
  rw [show (10 ^ 200 + 999786382 - (10 ^ 200 - 97283) : ℕ) = 999883665 by norm_num]
  norm_num

#print axioms row200_W_sub_qN_prime
#print axioms row200_W_sub_q1_not_prime

/-- P0037 Table 2 page 214, row log10 B = 210: W - B = 999686796, q_Nq - B = 999503869.
The definition of W on page 214 says W - q_Nq is prime. PROVED. -/
theorem row210_W_sub_qN_prime :
    (10 ^ 210 + 999686796 - (10 ^ 210 + 999503869) : ℕ).Prime := by
  rw [show (10 ^ 210 + 999686796 - (10 ^ 210 + 999503869) : ℕ) = 182927 by norm_num]
  norm_num

/-- P0037 Table 2 page 214, row log10 B = 210: B - q1 = 243203.
The definition of W on page 214 says W - q1 is composite; here W - q1 = 999929999,
divisible by 139. PROVED. -/
theorem row210_W_sub_q1_not_prime :
    ¬ (10 ^ 210 + 999686796 - (10 ^ 210 - 243203) : ℕ).Prime := by
  rw [show (10 ^ 210 + 999686796 - (10 ^ 210 - 243203) : ℕ) = 999929999 by norm_num]
  norm_num

#print axioms row210_W_sub_qN_prime
#print axioms row210_W_sub_q1_not_prime

/-- P0037 Table 2 page 214, row log10 B = 220: W - B = 999620578, q_Nq - B = 999530109.
The definition of W on page 214 says W - q_Nq is prime. PROVED. -/
theorem row220_W_sub_qN_prime :
    (10 ^ 220 + 999620578 - (10 ^ 220 + 999530109) : ℕ).Prime := by
  rw [show (10 ^ 220 + 999620578 - (10 ^ 220 + 999530109) : ℕ) = 90469 by norm_num]
  norm_num

/-- P0037 Table 2 page 214, row log10 B = 220: B - q1 = 177539.
The definition of W on page 214 says W - q1 is composite; here W - q1 = 999798117,
divisible by 3. PROVED. -/
theorem row220_W_sub_q1_not_prime :
    ¬ (10 ^ 220 + 999620578 - (10 ^ 220 - 177539) : ℕ).Prime := by
  rw [show (10 ^ 220 + 999620578 - (10 ^ 220 - 177539) : ℕ) = 999798117 by norm_num]
  norm_num

#print axioms row220_W_sub_qN_prime
#print axioms row220_W_sub_q1_not_prime

/-- P0037 Table 2 page 214, row log10 B = 230: W - B = 999983752, q_Nq - B = 999634941.
The definition of W on page 214 says W - q_Nq is prime. PROVED. -/
theorem row230_W_sub_qN_prime :
    (10 ^ 230 + 999983752 - (10 ^ 230 + 999634941) : ℕ).Prime := by
  rw [show (10 ^ 230 + 999983752 - (10 ^ 230 + 999634941) : ℕ) = 348811 by norm_num]
  norm_num

/-- P0037 Table 2 page 214, row log10 B = 230: B - q1 = 112643.
The definition of W on page 214 says W - q1 is composite; here W - q1 = 1000096395,
divisible by 3. PROVED. -/
theorem row230_W_sub_q1_not_prime :
    ¬ (10 ^ 230 + 999983752 - (10 ^ 230 - 112643) : ℕ).Prime := by
  rw [show (10 ^ 230 + 999983752 - (10 ^ 230 - 112643) : ℕ) = 1000096395 by norm_num]
  norm_num

#print axioms row230_W_sub_qN_prime
#print axioms row230_W_sub_q1_not_prime

/-- P0037 Table 2 page 214, row log10 B = 240: W - B = 999872854, q_Nq - B = 999836541.
The definition of W on page 214 says W - q_Nq is prime. PROVED. -/
theorem row240_W_sub_qN_prime :
    (10 ^ 240 + 999872854 - (10 ^ 240 + 999836541) : ℕ).Prime := by
  rw [show (10 ^ 240 + 999872854 - (10 ^ 240 + 999836541) : ℕ) = 36313 by norm_num]
  norm_num

/-- P0037 Table 2 page 214, row log10 B = 240: B - q1 = 191747.
The definition of W on page 214 says W - q1 is composite; here W - q1 = 1000064601,
divisible by 3. PROVED. -/
theorem row240_W_sub_q1_not_prime :
    ¬ (10 ^ 240 + 999872854 - (10 ^ 240 - 191747) : ℕ).Prime := by
  rw [show (10 ^ 240 + 999872854 - (10 ^ 240 - 191747) : ℕ) = 1000064601 by norm_num]
  norm_num

#print axioms row240_W_sub_qN_prime
#print axioms row240_W_sub_q1_not_prime

/-- P0037 Table 2 page 214, row log10 B = 250: W - B = 999991806, q_Nq - B = 999488509.
The definition of W on page 214 says W - q_Nq is prime. PROVED. -/
theorem row250_W_sub_qN_prime :
    (10 ^ 250 + 999991806 - (10 ^ 250 + 999488509) : ℕ).Prime := by
  rw [show (10 ^ 250 + 999991806 - (10 ^ 250 + 999488509) : ℕ) = 503297 by norm_num]
  norm_num

/-- P0037 Table 2 page 214, row log10 B = 250: B - q1 = 701699.
The definition of W on page 214 says W - q1 is composite; here W - q1 = 1000693505,
divisible by 5. PROVED. -/
theorem row250_W_sub_q1_not_prime :
    ¬ (10 ^ 250 + 999991806 - (10 ^ 250 - 701699) : ℕ).Prime := by
  rw [show (10 ^ 250 + 999991806 - (10 ^ 250 - 701699) : ℕ) = 1000693505 by norm_num]
  norm_num

#print axioms row250_W_sub_qN_prime
#print axioms row250_W_sub_q1_not_prime

/-- P0037 Table 2 page 214, row log10 B = 260: W - B = 999864924, q_Nq - B = 999837181.
The definition of W on page 214 says W - q_Nq is prime. PROVED. -/
theorem row260_W_sub_qN_prime :
    (10 ^ 260 + 999864924 - (10 ^ 260 + 999837181) : ℕ).Prime := by
  rw [show (10 ^ 260 + 999864924 - (10 ^ 260 + 999837181) : ℕ) = 27743 by norm_num]
  norm_num

/-- P0037 Table 2 page 214, row log10 B = 260: B - q1 = 174467.
The definition of W on page 214 says W - q1 is composite; here W - q1 = 1000039391,
divisible by 13. PROVED. -/
theorem row260_W_sub_q1_not_prime :
    ¬ (10 ^ 260 + 999864924 - (10 ^ 260 - 174467) : ℕ).Prime := by
  rw [show (10 ^ 260 + 999864924 - (10 ^ 260 - 174467) : ℕ) = 1000039391 by norm_num]
  norm_num

#print axioms row260_W_sub_qN_prime
#print axioms row260_W_sub_q1_not_prime

/-- P0037 Table 2 page 214, row log10 B = 270: W - B = 999697006, q_Nq - B = 999503997.
The definition of W on page 214 says W - q_Nq is prime. PROVED. -/
theorem row270_W_sub_qN_prime :
    (10 ^ 270 + 999697006 - (10 ^ 270 + 999503997) : ℕ).Prime := by
  rw [show (10 ^ 270 + 999697006 - (10 ^ 270 + 999503997) : ℕ) = 193009 by norm_num]
  norm_num

/-- P0037 Table 2 page 214, row log10 B = 270: B - q1 = 112643.
The definition of W on page 214 says W - q1 is composite; here W - q1 = 999809649,
divisible by 3. PROVED. -/
theorem row270_W_sub_q1_not_prime :
    ¬ (10 ^ 270 + 999697006 - (10 ^ 270 - 112643) : ℕ).Prime := by
  rw [show (10 ^ 270 + 999697006 - (10 ^ 270 - 112643) : ℕ) = 999809649 by norm_num]
  norm_num

#print axioms row270_W_sub_qN_prime
#print axioms row270_W_sub_q1_not_prime

/-- P0037 Table 2 page 214, row log10 B = 280: W - B = 999837064, q_Nq - B = 999714813.
The definition of W on page 214 says W - q_Nq is prime. PROVED. -/
theorem row280_W_sub_qN_prime :
    (10 ^ 280 + 999837064 - (10 ^ 280 + 999714813) : ℕ).Prime := by
  rw [show (10 ^ 280 + 999837064 - (10 ^ 280 + 999714813) : ℕ) = 122251 by norm_num]
  norm_num

/-- P0037 Table 2 page 214, row log10 B = 280: B - q1 = 32003.
The definition of W on page 214 says W - q1 is composite; here W - q1 = 999869067,
divisible by 3. PROVED. -/
theorem row280_W_sub_q1_not_prime :
    ¬ (10 ^ 280 + 999837064 - (10 ^ 280 - 32003) : ℕ).Prime := by
  rw [show (10 ^ 280 + 999837064 - (10 ^ 280 - 32003) : ℕ) = 999869067 by norm_num]
  norm_num

#print axioms row280_W_sub_qN_prime
#print axioms row280_W_sub_q1_not_prime

/-- P0037 Table 2 page 214, row log10 B = 290: W - B = 999872646, q_Nq - B = 999819517.
The definition of W on page 214 says W - q_Nq is prime. PROVED. -/
theorem row290_W_sub_qN_prime :
    (10 ^ 290 + 999872646 - (10 ^ 290 + 999819517) : ℕ).Prime := by
  rw [show (10 ^ 290 + 999872646 - (10 ^ 290 + 999819517) : ℕ) = 53129 by norm_num]
  norm_num

/-- P0037 Table 2 page 214, row log10 B = 290: B - q1 = 115331.
The definition of W on page 214 says W - q1 is composite; here W - q1 = 999987977,
divisible by 631. PROVED. -/
theorem row290_W_sub_q1_not_prime :
    ¬ (10 ^ 290 + 999872646 - (10 ^ 290 - 115331) : ℕ).Prime := by
  rw [show (10 ^ 290 + 999872646 - (10 ^ 290 - 115331) : ℕ) = 999987977 by norm_num]
  norm_num

#print axioms row290_W_sub_qN_prime
#print axioms row290_W_sub_q1_not_prime

/-- P0037 Table 2 page 214, row log10 B = 300: W - B = 999821434, q_Nq - B = 999692157.
The definition of W on page 214 says W - q_Nq is prime. PROVED. -/
theorem row300_W_sub_qN_prime :
    (10 ^ 300 + 999821434 - (10 ^ 300 + 999692157) : ℕ).Prime := by
  rw [show (10 ^ 300 + 999821434 - (10 ^ 300 + 999692157) : ℕ) = 129277 by norm_num]
  norm_num

/-- P0037 Table 2 page 214, row log10 B = 300: B - q1 = 32771.
The definition of W on page 214 says W - q1 is composite; here W - q1 = 999854205,
divisible by 3. PROVED. -/
theorem row300_W_sub_q1_not_prime :
    ¬ (10 ^ 300 + 999821434 - (10 ^ 300 - 32771) : ℕ).Prime := by
  rw [show (10 ^ 300 + 999821434 - (10 ^ 300 - 32771) : ℕ) = 999854205 by norm_num]
  norm_num

#print axioms row300_W_sub_qN_prime
#print axioms row300_W_sub_q1_not_prime

end LeanLab.DtRS1998.Decomp121bSecondTable2
