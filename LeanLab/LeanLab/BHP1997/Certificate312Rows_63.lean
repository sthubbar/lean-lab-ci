/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Certificate312Rows_62
import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_4032 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4032 j) = 405075813 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4033 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4033 j) = 406867056 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4034 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4034 j) = 408938571 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4035 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4035 j) = 410704923 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4036 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4036 j) = 412846877 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4037 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4037 j) = 414635809 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4038 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4038 j) = 416752529 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4039 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4039 j) = 418611227 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4040 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4040 j) = 420750473 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4041 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4041 j) = 422584254 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4042 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4042 j) = 424793940 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4043 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4043 j) = 426650635 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4044 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4044 j) = 428836033 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4045 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4045 j) = 430763611 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4046 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4046 j) = 432972578 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4047 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4047 j) = 434876275 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4048 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4048 j) = 437156801 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4049 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4049 j) = 439084181 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4050 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4050 j) = 441340603 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4051 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4051 j) = 443338960 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4052 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4052 j) = 445619078 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4053 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4053 j) = 447593571 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4054 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4054 j) = 449945334 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4055 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4055 j) = 451944008 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4056 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4056 j) = 454272575 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4057 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4057 j) = 456343381 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4058 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4058 j) = 458696839 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4059 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4059 j) = 460744889 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4060 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4060 j) = 463171181 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4061 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4061 j) = 465244600 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4062 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4062 j) = 467648865 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4063 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4063 j) = 469795632 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4064 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4064 j) = 472225199 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4065 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4065 j) = 474348885 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4066 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4066 j) = 476851069 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4067 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4067 j) = 478999734 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4068 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4068 j) = 481479400 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4069 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4069 j) = 483701215 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4070 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4070 j) = 486206575 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4071 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4071 j) = 488406337 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4072 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4072 j) = 490985648 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4073 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4073 j) = 493211649 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4074 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4074 j) = 495769649 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4075 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4075 j) = 498070139 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4076 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4076 j) = 500655141 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4077 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4077 j) = 502934887 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4078 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4078 j) = 505595166 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4079 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4079 j) = 507902459 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4080 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4080 j) = 510542804 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4081 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4081 j) = 512926007 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4082 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4082 j) = 515594702 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4083 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4083 j) = 517958534 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4084 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4084 j) = 520704004 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4085 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4085 j) = 523096828 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4086 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4086 j) = 525823739 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4087 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4087 j) = 528293935 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4088 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4088 j) = 531050757 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4089 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4089 j) = 533503046 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4090 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4090 j) = 536338145 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4091 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4091 j) = 538821011 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4092 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4092 j) = 541639060 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4093 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4093 j) = 544200897 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4094 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4094 j) = 547050495 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_4095 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4095 j) = 548868692 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel

/-- Page 51. Exact E2 row block 4032 through 4095. -/
theorem lowerTwo_rows312_63 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (4032+i) j) = 30282356910 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_4032, lowerTwo_row_4033, lowerTwo_row_4034, lowerTwo_row_4035, lowerTwo_row_4036, lowerTwo_row_4037, lowerTwo_row_4038, lowerTwo_row_4039, lowerTwo_row_4040, lowerTwo_row_4041, lowerTwo_row_4042, lowerTwo_row_4043, lowerTwo_row_4044, lowerTwo_row_4045, lowerTwo_row_4046, lowerTwo_row_4047, lowerTwo_row_4048, lowerTwo_row_4049, lowerTwo_row_4050, lowerTwo_row_4051, lowerTwo_row_4052, lowerTwo_row_4053, lowerTwo_row_4054, lowerTwo_row_4055, lowerTwo_row_4056, lowerTwo_row_4057, lowerTwo_row_4058, lowerTwo_row_4059, lowerTwo_row_4060, lowerTwo_row_4061, lowerTwo_row_4062, lowerTwo_row_4063, lowerTwo_row_4064, lowerTwo_row_4065, lowerTwo_row_4066, lowerTwo_row_4067, lowerTwo_row_4068, lowerTwo_row_4069, lowerTwo_row_4070, lowerTwo_row_4071, lowerTwo_row_4072, lowerTwo_row_4073, lowerTwo_row_4074, lowerTwo_row_4075, lowerTwo_row_4076, lowerTwo_row_4077, lowerTwo_row_4078, lowerTwo_row_4079, lowerTwo_row_4080, lowerTwo_row_4081, lowerTwo_row_4082, lowerTwo_row_4083, lowerTwo_row_4084, lowerTwo_row_4085, lowerTwo_row_4086, lowerTwo_row_4087, lowerTwo_row_4088, lowerTwo_row_4089, lowerTwo_row_4090, lowerTwo_row_4091, lowerTwo_row_4092, lowerTwo_row_4093, lowerTwo_row_4094, lowerTwo_row_4095, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
