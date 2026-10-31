/-
P0099, O. Ramaré and Y. Saouter, Short effective intervals containing primes,
J. Number Theory 98 (2003) 10-33. Copy: papers/P0099.pdf.

Unit U-6738, session 20261020T1914Z-cloud49. AI-written Lean code, Claude. Checked only by
the Lean kernel. Binary Goldbach is OPEN.

Lower halves of `MuStar48Bounds` and `MuStar55Bounds`, reduction.
* `cs`: Cauchy-Schwarz on [0, 1] for continuous functions. PROVED.
* `holder_w`: weighted Hölder, (∫ g^2 w)^3 ≤ (∫|g|)^2 ∫ g^4 w^3 for w ≥ 0 on [0, 1]. PROVED.
* `muStar_lower_of`: μ_m/2 ≤ μ*_m from the named integral inequality `HolderCert m`,
  0 < ∫ g^4 w^3 and ∫ g^2 · ∫ g^4 w^3 ≤ 4 (∫ g^2 w)^3 with g = f_m^(m), w = 4t(1-t). PROVED.
  A Python exact rational check gives 4 X^3/(S2 D) ≈ 1.5418 for m = 48 and 1.5419 for m = 55,
  so `HolderCert 48` and `HolderCert 55` hold numerically; the unweighted w = 1 gives only
  0.2516 · 4 and 0.2465 · 4, failing for m = 55.
* `holderCert_of`: `HolderCert m` from two rational inequalities on integer coefficient lists,
  with f_m^(m) computed as the m-fold list derivative of (4t - 4t^2)^m. PROVED.
* `holderCert48`: by `decide +kernel`, about 3.5 minutes. PROVED.
* `muStar48Bounds`: `MuStar48Bounds` outright. PROVED. `HolderCert 55` is not yet certified.
-/
import Mathlib
import LeanLab.RamareSaouter2003.MuStarUpper

namespace LeanLab.RamareSaouter2003.MuStarLower
open Real LeanLab.RamareSaouter2003.Smooth MeasureTheory

/-- Cauchy-Schwarz on [0, 1]. PROVED. -/
theorem cs (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (∫ t in (0 : ℝ)..1, u t * v t) ^ 2 ≤
      (∫ t in (0 : ℝ)..1, u t ^ 2) * ∫ t in (0 : ℝ)..1, v t ^ 2 := by
  set a := ∫ t in (0 : ℝ)..1, u t ^ 2
  set b := ∫ t in (0 : ℝ)..1, u t * v t
  set c := ∫ t in (0 : ℝ)..1, v t ^ 2
  have h : ∀ s : ℝ, 0 ≤ a - 2 * s * b + s ^ 2 * c := by
    intro s
    have h0 : 0 ≤ ∫ t in (0 : ℝ)..1, (u t - s * v t) ^ 2 :=
      intervalIntegral.integral_nonneg zero_le_one (fun t _ => sq_nonneg _)
    have hpt : ∀ t, (u t - s * v t) ^ 2 = (u t ^ 2 - (2 * s) * (u t * v t)) + s ^ 2 * v t ^ 2 := by
      intro t; ring
    simp_rw [hpt] at h0
    have i1 : IntervalIntegrable (fun t => u t ^ 2) volume 0 1 := (hu.pow 2).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun t => (2 * s) * (u t * v t)) volume 0 1 :=
      ((hu.mul hv).const_mul _).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun t => s ^ 2 * v t ^ 2) volume 0 1 :=
      ((hv.pow 2).const_mul _).intervalIntegrable _ _
    rw [intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h0
    linarith
  have hc : 0 ≤ c := intervalIntegral.integral_nonneg zero_le_one (fun t _ => sq_nonneg _)
  rcases hc.lt_or_eq with hc | hc
  · have := h (b / c)
    have e : a - 2 * (b / c) * b + (b / c) ^ 2 * c = (a * c - b ^ 2) / c := by
      field_simp; ring
    rw [e] at this
    have := (div_nonneg_iff.mp this)
    rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
    · nlinarith
    · linarith
  · by_cases hb : b = 0
    · rw [hb, ← hc]; simp
    · have := h ((a + 1) / (2 * b))
      rw [← hc] at this
      have e : a - 2 * ((a + 1) / (2 * b)) * b = -1 := by field_simp; ring
      nlinarith

/-- Weighted Hölder on [0, 1]. PROVED. -/
theorem holder_w (g w : ℝ → ℝ) (hg : Continuous g) (hw : Continuous w)
    (hw0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ w t) :
    (∫ t in (0 : ℝ)..1, g t ^ 2 * w t) ^ 3 ≤
      (∫ t in (0 : ℝ)..1, |g t|) ^ 2 * ∫ t in (0 : ℝ)..1, g t ^ 4 * w t ^ 3 := by
  set X := ∫ t in (0 : ℝ)..1, g t ^ 2 * w t
  set A := ∫ t in (0 : ℝ)..1, |g t|
  set C := ∫ t in (0 : ℝ)..1, |g t| ^ 3 * w t ^ 2
  set D := ∫ t in (0 : ℝ)..1, g t ^ 4 * w t ^ 3
  have hsq : ∀ t, √|g t| ^ 2 = |g t| := fun t => Real.sq_sqrt (abs_nonneg _)
  have h1 : X ^ 2 ≤ A * C := by
    have := cs (fun t => √|g t|) (fun t => |g t| * √|g t| * w t)
      (hg.abs.sqrt) ((hg.abs.mul hg.abs.sqrt).mul hw)
    have e1 : ∀ t, √|g t| * (|g t| * √|g t| * w t) = g t ^ 2 * w t := by
      intro t
      calc √|g t| * (|g t| * √|g t| * w t) = |g t| * √|g t| ^ 2 * w t := by ring
        _ = g t ^ 2 * w t := by rw [hsq, ← sq_abs (g t)]; ring
    have e2 : ∀ t, (|g t| * √|g t| * w t) ^ 2 = |g t| ^ 3 * w t ^ 2 := by
      intro t; have := hsq t; rw [mul_pow, mul_pow, this]; ring
    simp only [e1, e2, hsq] at this
    exact this
  have hIcc : ∀ t ∈ Set.uIcc (0 : ℝ) 1, 0 ≤ w t := by
    intro t ht; rw [Set.uIcc_of_le zero_le_one] at ht; exact hw0 t ht
  have h2 : C ^ 2 ≤ X * D := by
    have := cs (fun t => |g t| * √(w t)) (fun t => g t ^ 2 * w t * √(w t))
      (hg.abs.mul hw.sqrt) (((hg.pow 2).mul hw).mul hw.sqrt)
    have q : ∀ t ∈ Set.uIcc (0 : ℝ) 1, √(w t) ^ 2 = w t := fun t ht => Real.sq_sqrt (hIcc t ht)
    have c1 : (∫ t in (0 : ℝ)..1, (|g t| * √(w t)) * (g t ^ 2 * w t * √(w t))) = C :=
      intervalIntegral.integral_congr (fun t ht => by
        show _ = _
        calc |g t| * √(w t) * (g t ^ 2 * w t * √(w t))
            = |g t| * g t ^ 2 * w t * √(w t) ^ 2 := by ring
          _ = |g t| ^ 3 * w t ^ 2 := by rw [q t ht, ← sq_abs (g t)]; ring)
    have c2 : (∫ t in (0 : ℝ)..1, (|g t| * √(w t)) ^ 2) = X :=
      intervalIntegral.integral_congr (fun t ht => by
        rw [mul_pow, q t ht, sq_abs])
    have c3 : (∫ t in (0 : ℝ)..1, (g t ^ 2 * w t * √(w t)) ^ 2) = D :=
      intervalIntegral.integral_congr (fun t ht => by
        rw [mul_pow, q t ht]; ring)
    rw [c1, c2, c3] at this
    exact this
  have hA : 0 ≤ A := intervalIntegral.integral_nonneg zero_le_one (fun t _ => abs_nonneg _)
  have hC : 0 ≤ C := intervalIntegral.integral_nonneg zero_le_one
    (fun t ht => mul_nonneg (pow_nonneg (abs_nonneg _) _) (sq_nonneg _))
  have hD : 0 ≤ D := intervalIntegral.integral_nonneg zero_le_one
    (fun t ht => mul_nonneg (by positivity) (pow_nonneg (hw0 t ht) _))
  rcases le_or_gt X 0 with hX | hX
  · have : X ^ 3 ≤ 0 := by nlinarith [sq_nonneg X]
    nlinarith [sq_nonneg A]
  · have h3 : X ^ 4 ≤ A ^ 2 * (X * D) := by
      have : (X ^ 2) ^ 2 ≤ (A * C) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
      nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg A)]
    have : X * X ^ 3 ≤ X * (A ^ 2 * D) := by nlinarith
    exact le_of_mul_le_mul_left this hX

/-- The weight w = 4t(1-t). -/
noncomputable def wt (t : ℝ) : ℝ := 4 * t * (1 - t)

/-- The named exact inequality: with g = f_m^(m), 0 < ∫ g^4 w^3 and
∫ g^2 · ∫ g^4 w^3 ≤ 4 (∫ g^2 w)^3. -/
def HolderCert (m : ℕ) : Prop :=
  0 < (∫ t in (0 : ℝ)..1, iteratedDeriv m (fm m) t ^ 4 * wt t ^ 3) ∧
  (∫ t in (0 : ℝ)..1, iteratedDeriv m (fm m) t ^ 2) *
      (∫ t in (0 : ℝ)..1, iteratedDeriv m (fm m) t ^ 4 * wt t ^ 3) ≤
    4 * (∫ t in (0 : ℝ)..1, iteratedDeriv m (fm m) t ^ 2 * wt t) ^ 3


/-! ### Exact certificate by list polynomials over ℚ -/

def addL : List ℤ → List ℤ → List ℤ
  | [], k => k
  | a :: l, [] => a :: l
  | a :: l, b :: k => (a + b) :: addL l k

def mulL : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: l, k => addL (k.map (a * ·)) (0 :: mulL l k)

def derivL : List ℤ → List ℤ
  | [] => []
  | a :: l => addL l (0 :: derivL l)

def powL (l : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => mulL (powL l n) l

def intL : ℕ → List ℤ → ℚ
  | _, [] => 0
  | n, a :: l => (a : ℚ) / (n + 1) + intL (n + 1) l

noncomputable def ev : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: l, t => (a : ℝ) + t * ev l t

theorem ev_add (l k : List ℤ) (t : ℝ) : ev (addL l k) t = ev l t + ev k t := by
  induction l generalizing k with
  | nil => simp [addL, ev]
  | cons a l ih =>
    cases k with
    | nil => simp [addL, ev]
    | cons b k => simp only [addL, ev, ih]; push_cast; ring

theorem ev_map (c : ℤ) (k : List ℤ) (t : ℝ) : ev (k.map (c * ·)) t = c * ev k t := by
  induction k with
  | nil => simp [ev]
  | cons b k ih => simp only [List.map, ev, ih]; push_cast; ring

theorem ev_mul (l k : List ℤ) (t : ℝ) : ev (mulL l k) t = ev l t * ev k t := by
  induction l with
  | nil => simp [mulL, ev]
  | cons a l ih => simp only [mulL, ev_add, ev_map, ev, ih]; push_cast; ring

theorem ev_pow (l : List ℤ) (n : ℕ) (t : ℝ) : ev (powL l n) t = ev l t ^ n := by
  induction n with
  | zero => simp [powL, ev]
  | succ n ih => rw [powL, ev_mul, ih, pow_succ]

theorem ev_cont (l : List ℤ) : Continuous (ev l) := by
  induction l with
  | nil => exact continuous_const
  | cons a l ih => exact continuous_const.add (continuous_id.mul ih)

theorem ev_hasDeriv (l : List ℤ) (t : ℝ) : HasDerivAt (ev l) (ev (derivL l) t) t := by
  induction l with
  | nil => simp only [ev, derivL]; exact hasDerivAt_const t (0 : ℝ)
  | cons a l ih =>
    have h := ((hasDerivAt_id t).mul ih).const_add (a : ℝ)
    simp only [derivL, ev_add, ev]
    convert h using 1
    all_goals first
      | rfl
      | (show _ = 1 * ev l t + t * ev (derivL l) t; push_cast; ring)

theorem iter_ev (l : List ℤ) (n : ℕ) : iteratedDeriv n (ev l) = ev (derivL^[n] l) := by
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ', Function.iterate_succ_apply]
    have : deriv (ev l) = ev (derivL l) := funext fun t => (ev_hasDeriv l t).deriv
    rw [this, ih]

theorem int_ev (l : List ℤ) (n : ℕ) :
    ∫ t in (0 : ℝ)..1, t ^ n * ev l t = (intL n l : ℝ) := by
  induction l generalizing n with
  | nil => simp [ev, intL]
  | cons a l ih =>
    have hpt : ∀ t : ℝ, t ^ n * ev (a :: l) t = (a : ℝ) * t ^ n + t ^ (n + 1) * ev l t := by
      intro t; simp only [ev]; ring
    simp_rw [hpt]
    have i1 : IntervalIntegrable (fun t : ℝ => (a : ℝ) * t ^ n) volume 0 1 :=
      (continuous_const.mul (continuous_pow n)).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun t : ℝ => t ^ (n + 1) * ev l t) volume 0 1 :=
      ((continuous_pow _).mul (ev_cont l)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add i1 i2, ih,
      intervalIntegral.integral_const_mul, integral_pow]
    simp only [intL]; push_cast; ring

def wL : List ℤ := [0, 4, -4]
def fL (m : ℕ) : List ℤ := powL wL m
def gL (m : ℕ) : List ℤ := derivL^[m] (fL m)

theorem wt_ev (t : ℝ) : wt t = ev wL t := by simp [wt, wL, ev]; ring

theorem g_ev (m : ℕ) : iteratedDeriv m (fm m) = ev (gL m) := by
  have : fm m = ev (fL m) := by
    funext t; rw [fL, ev_pow, ← wt_ev]; simp [fm, wt]
  rw [this, iter_ev]; rfl

theorem holderCert_of (m : ℕ)
    (h1 : 0 < intL 0 (mulL (powL (gL m) 4) (powL wL 3)))
    (h2 : intL 0 (powL (gL m) 2) * intL 0 (mulL (powL (gL m) 4) (powL wL 3)) ≤
      4 * intL 0 (mulL (powL (gL m) 2) wL) ^ 3) : HolderCert m := by
  have e : ∀ L : List ℤ, ∫ t in (0 : ℝ)..1, ev L t = (intL 0 L : ℝ) := by
    intro L; rw [← int_ev L 0]; simp
  have e4 : (∫ t in (0 : ℝ)..1, iteratedDeriv m (fm m) t ^ 4 * wt t ^ 3) =
      (intL 0 (mulL (powL (gL m) 4) (powL wL 3)) : ℝ) := by
    rw [← e]; congr 1; funext t; rw [g_ev, ev_mul, ev_pow, ev_pow, wt_ev]
  have e2 : (∫ t in (0 : ℝ)..1, iteratedDeriv m (fm m) t ^ 2) = (intL 0 (powL (gL m) 2) : ℝ) := by
    rw [← e]; congr 1; funext t; rw [g_ev, ev_pow]
  have e2w : (∫ t in (0 : ℝ)..1, iteratedDeriv m (fm m) t ^ 2 * wt t) =
      (intL 0 (mulL (powL (gL m) 2) wL) : ℝ) := by
    rw [← e]; congr 1; funext t; rw [g_ev, ev_mul, ev_pow, wt_ev]
  refine ⟨?_, ?_⟩
  · rw [e4]; exact_mod_cast h1
  · rw [e4, e2, e2w]; exact_mod_cast h2

theorem cert48a : 0 < intL 0 (mulL (powL (gL 48) 4) (powL wL 3)) := by decide +kernel
theorem cert48b : intL 0 (powL (gL 48) 2) * intL 0 (mulL (powL (gL 48) 4) (powL wL 3)) ≤
      4 * intL 0 (mulL (powL (gL 48) 2) wL) ^ 3 := by decide +kernel

/-- `HolderCert 48`. PROVED by exact rational arithmetic. -/
theorem holderCert48 : HolderCert 48 := holderCert_of 48 cert48a cert48b

/-- μ_m/2 ≤ μ*_m CONDITIONAL ON `HolderCert m`. PROVED. -/
theorem muStar_lower_of (m : ℕ) (hc : HolderCert m) :
    (Nat.factorial (2 * m + 1) : ℝ) / ((Nat.factorial m : ℝ) * √(2 * m + 1)) / 2 ≤ muStar m := by
  obtain ⟨hD, hI⟩ := hc
  set g := iteratedDeriv m (fm m)
  set A := ∫ t in (0 : ℝ)..1, |g t|
  set B := ∫ t in (0 : ℝ)..1, fm m t
  set S := ∫ t in (0 : ℝ)..1, g t ^ 2
  set X := ∫ t in (0 : ℝ)..1, g t ^ 2 * wt t
  set D := ∫ t in (0 : ℝ)..1, g t ^ 4 * wt t ^ 3
  set μ := (Nat.factorial (2 * m + 1) : ℝ) / ((Nat.factorial m : ℝ) * √(2 * m + 1))
  have hcont : Continuous g := by
    simp only [g]; rw [MuStarUpper.iteratedDeriv_fm]; exact (Polynomial.derivative^[m] _).continuous
  have hH : X ^ 3 ≤ A ^ 2 * D := holder_w g wt hcont (by unfold wt; fun_prop)
    (fun t ht => by unfold wt; have := ht.1; have := ht.2; nlinarith)
  have hS : S ≤ 4 * A ^ 2 := by
    have : S * D ≤ (4 * A ^ 2) * D := by nlinarith
    exact le_of_mul_le_mul_right this hD
  have hB : B = 2 ^ (2 * m) * (m.factorial : ℝ) ^ 2 / (2 * m + 1).factorial := norm_fm m
  have hf0 : (0 : ℝ) < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hf1 : (0 : ℝ) < (Nat.factorial (2 * m + 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hs0 : (0 : ℝ) < √(2 * m + 1) := Real.sqrt_pos.mpr (by positivity)
  have hss : √(2 * m + 1) ^ 2 = (2 * m + 1 : ℝ) := Real.sq_sqrt (by positivity)
  have hBpos : 0 < B := by rw [hB]; positivity
  have hμ0 : 0 ≤ μ := by positivity
  have hfac : (Nat.factorial (2 * m + 1) : ℝ) = (2 * m + 1) * Nat.factorial (2 * m) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hkey : (B * μ) ^ 2 = S := by
    simp only [S, g]
    rw [MuStarUpper.l2_identity]
    change (B * μ) ^ 2 = _ * B
    simp only [μ]
    rw [hB]
    simp only [mul_pow, div_pow]
    rw [hss, hfac]
    rw [hfac] at hf1
    have h2 : (0 : ℝ) < 2 * m + 1 := by positivity
    have h3 : (0 : ℝ) < (Nat.factorial (2 * m) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [show (2 : ℝ) ^ (2 * m) = 4 ^ m by rw [pow_mul]; norm_num]
    field_simp
  have hA0 : 0 ≤ A := intervalIntegral.integral_nonneg zero_le_one (fun t _ => abs_nonneg _)
  have hAle : B * μ / 2 ≤ A := by
    have hBμ : 0 ≤ B * μ := mul_nonneg hBpos.le hμ0
    nlinarith
  show μ / 2 ≤ A / B
  rw [le_div_iff₀ hBpos]; linarith

/-- Lower half of `MuStar48Bounds` CONDITIONAL ON `HolderCert 48`. PROVED. -/
theorem muStar48_lower_of (hc : HolderCert 48) :
    LeanLab.RamareSaouter2003.Row1.mu48 / 2 ≤ muStar 48 := by
  have h := muStar_lower_of 48 hc
  simp only [LeanLab.RamareSaouter2003.Row1.mu48]
  convert h using 4; norm_num

/-- Lower half of `MuStar55Bounds` CONDITIONAL ON `HolderCert 55`. PROVED. -/
theorem muStar55_lower_of (hc : HolderCert 55) :
    LeanLab.RamareSaouter2003.Row59.mu55 / 2 ≤ muStar 55 := by
  have h := muStar_lower_of 55 hc
  simp only [LeanLab.RamareSaouter2003.Row59.mu55]
  convert h using 4; norm_num

theorem muStar48Bounds_of_cert (hc : HolderCert 48) : LeanLab.RamareSaouter2003.Row1.MuStar48Bounds :=
  MuStarUpper.muStar48Bounds_of_lower (muStar48_lower_of hc)

theorem muStar55Bounds_of_cert (hc : HolderCert 55) : LeanLab.RamareSaouter2003.Row59.MuStar55Bounds :=
  MuStarUpper.muStar55Bounds_of_lower (muStar55_lower_of hc)

/-- `MuStar48Bounds`, μ_48/2 ≤ μ*_48 ≤ μ_48. PROVED outright. -/
theorem muStar48Bounds : LeanLab.RamareSaouter2003.Row1.MuStar48Bounds :=
  muStar48Bounds_of_cert holderCert48

end LeanLab.RamareSaouter2003.MuStarLower

#print axioms LeanLab.RamareSaouter2003.MuStarLower.holder_w
#print axioms LeanLab.RamareSaouter2003.MuStarLower.holderCert48
#print axioms LeanLab.RamareSaouter2003.MuStarLower.muStar48Bounds
#print axioms LeanLab.RamareSaouter2003.MuStarLower.muStar48Bounds_of_cert
#print axioms LeanLab.RamareSaouter2003.MuStarLower.muStar55Bounds_of_cert
