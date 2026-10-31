/-
R-5280, CLOUD 20261020T2113Z-cloud51, unit U-6735, T3 MOONSHOT.
AI wrote this Lean code. Not progress on binary Goldbach, which is OPEN.

The automata route.  For a k-automatic set A, "every even N ≥ 4 is in A + A"
is decidable, Büchi-Bruyère, Walnut.  The primes are not automatic, and no
automatic set can sit inside them, while automatic restrictions of the primes
carry their own digital local obstructions.
* `ofDigits_pump`: the value of the pumped word z y^i x, little endian, is
  t + s * w i with w (i+1) = c + b^|y| * w i.
* `affine_return`: modulo a prime q not dividing M, an orbit of the affine map
  w ↦ c + M w returns to its start.
* `pumped_not_all_prime`: such an increasing affine family is never all prime.
* `no_pumped_prime_family`: for every base b ≥ 2 and words x, y, z with y
  nonempty and x of positive value, some z y^i x is composite; so no infinite
  regular language of base b numerals lies inside the primes, Hartmanis-Shank
  1968, KNOWN.
* `s2_pow_sub`: for odd p ≤ 2^k, s₂(p) + s₂(2^k - p) = k + 1.
* `evil_goldbach_fails_pow4`: 4^j is never a sum of two primes of even binary
  digit sum, the Thue-Morse local obstruction.
-/
import Mathlib

namespace LeanLab.Routes.R5280

/-- Binary digit sum. -/
def s2 (n : ℕ) : ℕ := (Nat.digits 2 n).sum

theorem ofDigits_pump (b : ℕ) (x y z : List ℕ) (i : ℕ) :
    Nat.ofDigits b (z ++ (List.replicate i y).flatten ++ x)
      = Nat.ofDigits b z + b ^ z.length * Nat.ofDigits b ((List.replicate i y).flatten ++ x)
    ∧ Nat.ofDigits b ((List.replicate (i + 1) y).flatten ++ x)
      = Nat.ofDigits b y + b ^ y.length * Nat.ofDigits b ((List.replicate i y).flatten ++ x) := by
  constructor
  · rw [List.append_assoc, Nat.ofDigits_append]
  · rw [List.replicate_succ, List.flatten_cons, List.append_assoc, Nat.ofDigits_append]

theorem affine_return (q M c : ℕ) [Fact q.Prime] (hq : ¬ q ∣ M) (w : ℕ → ℕ)
    (hw : ∀ i, w (i + 1) = c + M * w i) :
    ∃ T, 0 < T ∧ ((w T : ℕ) : ZMod q) = (w 0 : ZMod q) := by
  have hM : (M : ZMod q) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  have back : ∀ i j, ((w (i + 1) : ℕ) : ZMod q) = (w (j + 1) : ZMod q) →
      ((w i : ℕ) : ZMod q) = (w j : ZMod q) := by
    intro i j h
    rw [hw, hw] at h
    push_cast at h
    have h2 : (M : ZMod q) * w i = M * w j := add_left_cancel h
    exact mul_left_cancel₀ hM h2
  have down : ∀ i d, ((w i : ℕ) : ZMod q) = (w (i + d) : ZMod q) →
      ((w 0 : ℕ) : ZMod q) = (w d : ZMod q) := by
    intro i
    induction i with
    | zero => intro d h; simpa using h
    | succ i ih =>
      intro d h
      apply ih d
      apply back
      rw [show i + d + 1 = i + 1 + d by omega]
      exact h
  obtain ⟨i, j, hij, hEq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => ((w n : ℕ) : ZMod q))
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · refine ⟨j - i, by omega, ?_⟩
    have := down i (j - i) (by rw [show i + (j - i) = j by omega]; exact hEq)
    exact this.symm
  · refine ⟨i - j, by omega, ?_⟩
    have := down j (i - j) (by rw [show j + (i - j) = i by omega]; exact hEq.symm)
    exact this.symm

theorem pumped_not_all_prime (b L c s t : ℕ) (hb : 2 ≤ b) (hL : 1 ≤ L) (hs : 1 ≤ s)
    (w : ℕ → ℕ) (hw : ∀ i, w (i + 1) = c + b ^ L * w i) (hw0 : 1 ≤ w 0) :
    ¬ ∀ i, (t + s * w i).Prime := by
  intro hall
  have hML : 2 ≤ b ^ L := le_trans hb (Nat.le_self_pow (by omega) b)
  have wpos : ∀ i, 1 ≤ w i := by
    intro i
    induction i with
    | zero => exact hw0
    | succ i ih => rw [hw]; nlinarith
  have wlt : ∀ i, w i < w (i + 1) := by
    intro i; rw [hw]; have := wpos i; nlinarith
  set n : ℕ → ℕ := fun i => t + s * w i with hn
  have nmono : StrictMono n := by
    apply strictMono_nat_of_lt_succ
    intro i
    simp only [hn]
    have := wlt i
    have : s * w i < s * w (i + 1) := Nat.mul_lt_mul_of_pos_left this (by omega)
    omega
  set k := b + 1
  have hnk : b < n k := by
    have h1 : b ≤ n b := nmono.id_le b
    have h2 : n b < n k := nmono (by omega)
    omega
  have hq : (n k).Prime := hall k
  haveI : Fact (n k).Prime := ⟨hq⟩
  have hndvd : ¬ n k ∣ b ^ L := by
    intro h
    have := hq.dvd_of_dvd_pow h
    have := Nat.le_of_dvd (by omega) this
    omega
  obtain ⟨T, hT, hret⟩ := affine_return (n k) (b ^ L) c hndvd (fun i => w (k + i))
    (by intro i; show w (k + (i + 1)) = c + b ^ L * w (k + i); rw [show k + (i + 1) = (k + i) + 1 by omega, hw])
  simp only [Nat.add_zero] at hret
  have hdvd : n k ∣ n (k + T) := by
    have h0 : ((n (k + T) : ℕ) : ZMod (n k)) = 0 := by
      have hself : ((n k : ℕ) : ZMod (n k)) = 0 := ZMod.natCast_self _
      simp only [hn] at hself ⊢
      push_cast at hself ⊢
      rw [hret]; exact hself
    exact (ZMod.natCast_eq_zero_iff _ _).1 h0
  have hp2 : (n (k + T)).Prime := hall (k + T)
  have := (Nat.prime_dvd_prime_iff_eq hq hp2).1 hdvd
  have := nmono (show k < k + T by omega)
  omega

/-- No infinite pumped family of base b numerals, hence no infinite regular
language of numerals, lies inside the primes. Digits are little endian:
z is the low part, x the leading part. -/
theorem no_pumped_prime_family (b : ℕ) (hb : 2 ≤ b) (x y z : List ℕ) (hy : y ≠ [])
    (hx : 0 < Nat.ofDigits b x) :
    ¬ ∀ i, (Nat.ofDigits b (z ++ (List.replicate i y).flatten ++ x)).Prime := by
  intro hall
  have hL : 1 ≤ y.length := List.length_pos_iff.mpr hy
  have hs : 1 ≤ b ^ z.length := Nat.one_le_pow _ _ (by omega)
  refine pumped_not_all_prime b y.length (Nat.ofDigits b y) (b ^ z.length) (Nat.ofDigits b z)
    hb hL hs (fun i => Nat.ofDigits b ((List.replicate i y).flatten ++ x))
    (fun i => (ofDigits_pump b x y z i).2)
    (by simp only [List.replicate_zero, List.flatten_nil, List.nil_append]; exact hx) ?_
  intro i
  rw [← (ofDigits_pump b x y z i).1]
  exact hall i

theorem s2_bit (r y : ℕ) (hr : r < 2) : s2 (r + 2 * y) = r + s2 y := by
  unfold s2
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h
    rcases Nat.eq_zero_or_pos y with hy | hy
    · subst hy; simp
    · rw [Nat.digits_add 2 (by norm_num) 0 y (by norm_num) (Or.inr (by omega))]
      simp
  · rw [Nat.digits_add 2 (by norm_num) r y hr (Or.inl (by omega))]
    simp

theorem s2_compl (k : ℕ) : ∀ a, a < 2 ^ k → s2 a + s2 (2 ^ k - 1 - a) = k := by
  induction k with
  | zero => intro a ha; simp at ha; subst ha; simp [s2]
  | succ k ih =>
    intro a ha
    obtain ⟨r, m, hr, rfl⟩ : ∃ r m, r < 2 ∧ a = r + 2 * m :=
      ⟨a % 2, a / 2, Nat.mod_lt _ (by norm_num), by omega⟩
    have hb : m < 2 ^ k := by rw [pow_succ] at ha; omega
    have e2 : 2 ^ (k + 1) - 1 - (r + 2 * m) = (1 - r) + 2 * (2 ^ k - 1 - m) := by
      rw [pow_succ]; omega
    rw [e2, s2_bit _ _ hr, s2_bit (1 - r) _ (by omega)]
    have := ih m hb
    omega

theorem s2_pow_sub (k p : ℕ) (hp : Odd p) (hpk : p ≤ 2 ^ k) :
    s2 p + s2 (2 ^ k - p) = k + 1 := by
  obtain ⟨m, rfl⟩ := hp
  have h1 : s2 (2 * m + 1) = 1 + s2 m := by
    rw [show 2 * m + 1 = 1 + 2 * m by ring, s2_bit 1 m (by norm_num)]
  have h0 : s2 (2 * m) = s2 m := by
    have := s2_bit 0 m (by norm_num); simpa using this
  have hc := s2_compl k (2 * m) (by omega)
  rw [show 2 ^ k - (2 * m + 1) = 2 ^ k - 1 - 2 * m by omega, h1]
  omega

/-- The Thue-Morse local obstruction: 4^j is never p + q with p, q prime
and both binary digit sums even. -/
theorem evil_goldbach_fails_pow4 (j : ℕ) (p q : ℕ) (hp : p.Prime) (_hq : q.Prime)
    (hpq : p + q = 4 ^ j) (hep : Even (s2 p)) (heq : Even (s2 q)) : False := by
  have h2 : s2 2 = 1 := by decide
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd' with h | h
    · subst h; rw [h2] at hep; exact absurd hep (by decide)
    · exact h
  have hk : (4 : ℕ) ^ j = 2 ^ (2 * j) := by rw [pow_mul]; norm_num
  have hs := s2_pow_sub (2 * j) p hpodd (by omega)
  rw [show 2 ^ (2 * j) - p = q by omega] at hs
  have : Even (s2 p + s2 q) := hep.add heq
  rw [hs] at this
  exact (Nat.not_even_iff_odd.mpr ⟨j, by ring⟩) this

end LeanLab.Routes.R5280

#print axioms LeanLab.Routes.R5280.ofDigits_pump
#print axioms LeanLab.Routes.R5280.affine_return
#print axioms LeanLab.Routes.R5280.pumped_not_all_prime
#print axioms LeanLab.Routes.R5280.no_pumped_prime_family
#print axioms LeanLab.Routes.R5280.s2_bit
#print axioms LeanLab.Routes.R5280.s2_compl
#print axioms LeanLab.Routes.R5280.s2_pow_sub
#print axioms LeanLab.Routes.R5280.evil_goldbach_fails_pow4
