import LeanLab.Song2020.Audit139
open LeanLab.Song2020 LeanLab.Song2020.State1562
-- exponent of the Lemma4-times-Lemma5 product relative to y^2 at the window floor y = n^theta:
-- n-exponent of 2D(A+B): (21/31 - 14g/31 + e) + (1 - g); y-exponent: 23/31 + 1 = 54/31
-- at y = n^theta the total n-exponent is sum + (54/31)*theta; Audit139 says this is theta*8/31 + e
example (γ ε : ℝ) : (21/31 - 14*γ/31 + ε) + (1 - γ) + (54/31) * ((52 - 45*γ)/8) - 2*((52 - 45*γ)/8) = (8/31)*((52 - 45*γ)/8) - (52 - 45*γ)/8 + ε := by ring
#check @Chebyshev.eventually_primeCounting_le
#check @LeanLab.Song2020.Audit139.threshold_exponent_loss139
#check @LeanLab.Song2020.Audit139.positive_power_not_log_saving139
#check @LeanLab.Song2020.Audit139.all_epsilon_bounds_not_log_saving139
#check @LeanLab.Song2020.Audit139.threshold_exponent_margin139
