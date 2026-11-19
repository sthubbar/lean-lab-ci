/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_28.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/2744bfa9-9f29-47d4-be96-659b2a91a91b
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData28.s0 : Seg := ⟨345371419552240618977708317, 345371419552240625527127014, 18726915, 4096, [], 345529269229724388453627391, 345529269229724395006039159⟩
def PrimData28.s1 : Seg := ⟨345529269229724388453627391, 345529269229724395006039159, 18735107, 4096, [], 345685578441476842336134983, 345685578441476848891511371⟩
def PrimData28.s2 : Seg := ⟨345685578441476842336134983, 345685578441476848891511371, 18743299, 4096, [], 345830152789561765305000732, 345830152789561771863117112⟩
def PrimData28.s3 : Seg := ⟨345830152789561765305000732, 345830152789561771863117112, 18751491, 4096, [], 345984616561507554627601433, 345984616561507561188647525⟩
def PrimData28.s4 : Seg := ⟨345984616561507554627601433, 345984616561507561188647525, 18759683, 4096, [], 346140011194067018889797938, 346140011194067025453790378⟩
def PrimData28.s5 : Seg := ⟨346140011194067018889797938, 346140011194067025453790378, 18767875, 4096, [], 346292011545020456830513562, 346292011545020463397389500⟩
def PrimData28.s6 : Seg := ⟨346292011545020456830513562, 346292011545020463397389500, 18776067, 4096, [], 346438454695154703608841313, 346438454695154710178494272⟩
def PrimData28.s7 : Seg := ⟨346438454695154703608841313, 346438454695154710178494272, 18784259, 4096, [], 346594170485628548384834484, 346594170485628554957441530⟩
def PrimData28.s8 : Seg := ⟨346594170485628548384834484, 346594170485628554957441530, 18792451, 4096, [], 346736295759651490849499114, 346736295759651497424801213⟩
def PrimData28.s9 : Seg := ⟨346736295759651490849499114, 346736295759651497424801213, 18800643, 4096, [], 346885840082989224972377916, 346885840082989231550515825⟩
def PrimData28.s10 : Seg := ⟨346885840082989224972377916, 346885840082989231550515825, 18808835, 4096, [], 347034770335195337583437752, 347034770335195344164400624⟩
def PrimData28.s11 : Seg := ⟨347034770335195337583437752, 347034770335195344164400624, 18817027, 4096, [], 347186176435985991268529709, 347186176435985997852364447⟩
def PrimData28.s12 : Seg := ⟨347186176435985991268529709, 347186176435985997852364447, 18825219, 4096, [], 347337277374770404547734750, 347337277374770411134436335⟩
def PrimData28.s13 : Seg := ⟨347337277374770404547734750, 347337277374770411134436335, 18833411, 4096, [], 347493017358105329189781222, 347493017358105335779438046⟩
def PrimData28.s14 : Seg := ⟨347493017358105329189781222, 347493017358105335779438046, 18841603, 4096, [], 347641036092220252359198170, 347641036092220258951663949⟩
def PrimData28.s15 : Seg := ⟨347641036092220252359198170, 347641036092220258951663949, 18849795, 4096, [], 347797402228164447910177316, 347797402228164454505609763⟩
def PrimData28.s16 : Seg := ⟨347797402228164447910177316, 347797402228164454505609763, 18857987, 4096, [], 347947900858020748833039535, 347947900858020755431327356⟩
def PrimData28.s17 : Seg := ⟨347947900858020748833039535, 347947900858020755431327356, 18866179, 4096, [], 348104275145684951434150050, 348104275145684958035404539⟩
def PrimData28.s18 : Seg := ⟨348104275145684951434150050, 348104275145684958035404539, 18874371, 4096, [], 348252309221573839440236710, 348252309221573846044298471⟩
def PrimData28.s19 : Seg := ⟨348252309221573839440236710, 348252309221573846044298471, 18882563, 4096, [], 348394475020082817897767018, 348394475020082824504526445⟩
def PrimData28.s20 : Seg := ⟨348394475020082817897767018, 348394475020082824504526445, 18890755, 4096, [], 348546534589451181121097646, 348546534589451187730741614⟩
def PrimData28.s21 : Seg := ⟨348546534589451181121097646, 348546534589451187730741614, 18898947, 4096, [], 348684998818127584460766014, 348684998818127591073035739⟩
def PrimData28.s22 : Seg := ⟨348684998818127584460766014, 348684998818127591073035739, 18907139, 4096, [], 348842320547776686787838678, 348842320547776693403092120⟩
def PrimData28.s23 : Seg := ⟨348842320547776686787838678, 348842320547776693403092120, 18915331, 4096, [], 348994700972478695400961712, 348994700972478702019105336⟩
def PrimData28.s24 : Seg := ⟨348994700972478695400961712, 348994700972478702019105336, 18923523, 4096, [], 349151412741396094872537139, 349151412741396101493653291⟩
def PrimData28.s25 : Seg := ⟨349151412741396094872537139, 349151412741396101493653291, 18931715, 4096, [], 349307819380228126856375272, 349307819380228133480457392⟩
def PrimData28.s26 : Seg := ⟨349307819380228126856375272, 349307819380228133480457392, 18939907, 4096, [], 349459902523528562507807772, 349459902523528569134773809⟩
def PrimData28.s27 : Seg := ⟨349459902523528562507807772, 349459902523528569134773809, 18948099, 4096, [], 349609207403742490313497091, 349609207403742496943294535⟩
def PrimData28.s28 : Seg := ⟨349609207403742490313497091, 349609207403742496943294535, 18956291, 4096, [], 349761607501066736741944850, 349761607501066743374632732⟩
def PrimData28.s29 : Seg := ⟨349761607501066736741944850, 349761607501066743374632732, 18964483, 4096, [], 349908447081168167481596996, 349908447081168174117068296⟩
def PrimData28.s30 : Seg := ⟨349908447081168167481596996, 349908447081168174117068296, 18972675, 4096, [], 350056836187701235473708839, 350056836187701242111993512⟩
def PrimData28.s31 : Seg := ⟨350056836187701235473708839, 350056836187701242111993512, 18980867, 4096, [], 350215431122676266705385618, 350215431122676273346678543⟩
def PrimData28.s32 : Seg := ⟨350215431122676266705385618, 350215431122676273346678543, 18989059, 4096, [], 350366919464352497169689922, 350366919464352503813856004⟩
def PrimData28.s33 : Seg := ⟨350366919464352497169689922, 350366919464352503813856004, 18997251, 4096, [], 350513774161225714086072348, 350513774161225720733023005⟩
def PrimData28.s34 : Seg := ⟨350513774161225714086072348, 350513774161225720733023005, 19005443, 4096, [], 350664342769958929402594830, 350664342769958936052401021⟩

def PrimData28.segs : List Seg := [PrimData28.s0, PrimData28.s1, PrimData28.s2, PrimData28.s3, PrimData28.s4, PrimData28.s5, PrimData28.s6, PrimData28.s7, PrimData28.s8, PrimData28.s9, PrimData28.s10, PrimData28.s11, PrimData28.s12, PrimData28.s13, PrimData28.s14, PrimData28.s15, PrimData28.s16, PrimData28.s17, PrimData28.s18, PrimData28.s19, PrimData28.s20, PrimData28.s21, PrimData28.s22, PrimData28.s23, PrimData28.s24, PrimData28.s25, PrimData28.s26, PrimData28.s27, PrimData28.s28, PrimData28.s29, PrimData28.s30, PrimData28.s31, PrimData28.s32, PrimData28.s33, PrimData28.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked28_s0 : Seg.bok PrimData28.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s0

theorem checked28_s1 : Seg.bok PrimData28.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s1

theorem checked28_s2 : Seg.bok PrimData28.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s2

theorem checked28_s3 : Seg.bok PrimData28.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s3

theorem checked28_s4 : Seg.bok PrimData28.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s4

theorem checked28_s5 : Seg.bok PrimData28.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s5

theorem checked28_s6 : Seg.bok PrimData28.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s6

theorem checked28_s7 : Seg.bok PrimData28.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s7

theorem checked28_s8 : Seg.bok PrimData28.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s8

theorem checked28_s9 : Seg.bok PrimData28.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s9

theorem checked28_s10 : Seg.bok PrimData28.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s10

theorem checked28_s11 : Seg.bok PrimData28.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s11

theorem checked28_s12 : Seg.bok PrimData28.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s12

theorem checked28_s13 : Seg.bok PrimData28.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s13

theorem checked28_s14 : Seg.bok PrimData28.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s14

theorem checked28_s15 : Seg.bok PrimData28.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s15

theorem checked28_s16 : Seg.bok PrimData28.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s16

theorem checked28_s17 : Seg.bok PrimData28.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s17

theorem checked28_s18 : Seg.bok PrimData28.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s18

theorem checked28_s19 : Seg.bok PrimData28.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s19

theorem checked28_s20 : Seg.bok PrimData28.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s20

theorem checked28_s21 : Seg.bok PrimData28.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s21

theorem checked28_s22 : Seg.bok PrimData28.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s22

theorem checked28_s23 : Seg.bok PrimData28.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s23

theorem checked28_s24 : Seg.bok PrimData28.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s24

theorem checked28_s25 : Seg.bok PrimData28.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s25

theorem checked28_s26 : Seg.bok PrimData28.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s26

theorem checked28_s27 : Seg.bok PrimData28.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s27

theorem checked28_s28 : Seg.bok PrimData28.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s28

theorem checked28_s29 : Seg.bok PrimData28.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s29

theorem checked28_s30 : Seg.bok PrimData28.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s30

theorem checked28_s31 : Seg.bok PrimData28.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s31

theorem checked28_s32 : Seg.bok PrimData28.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s32

theorem checked28_s33 : Seg.bok PrimData28.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s33

theorem checked28_s34 : Seg.bok PrimData28.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28_s34

 theorem checked28 : ∀ s ∈ PrimData28.segs, (Seg.bok s) = true := by
  unfold PrimData28.segs
  exact List.forall_mem_cons.2 ⟨checked28_s0, List.forall_mem_cons.2 ⟨checked28_s1, List.forall_mem_cons.2 ⟨checked28_s2, List.forall_mem_cons.2 ⟨checked28_s3, List.forall_mem_cons.2 ⟨checked28_s4, List.forall_mem_cons.2 ⟨checked28_s5, List.forall_mem_cons.2 ⟨checked28_s6, List.forall_mem_cons.2 ⟨checked28_s7, List.forall_mem_cons.2 ⟨checked28_s8, List.forall_mem_cons.2 ⟨checked28_s9, List.forall_mem_cons.2 ⟨checked28_s10, List.forall_mem_cons.2 ⟨checked28_s11, List.forall_mem_cons.2 ⟨checked28_s12, List.forall_mem_cons.2 ⟨checked28_s13, List.forall_mem_cons.2 ⟨checked28_s14, List.forall_mem_cons.2 ⟨checked28_s15, List.forall_mem_cons.2 ⟨checked28_s16, List.forall_mem_cons.2 ⟨checked28_s17, List.forall_mem_cons.2 ⟨checked28_s18, List.forall_mem_cons.2 ⟨checked28_s19, List.forall_mem_cons.2 ⟨checked28_s20, List.forall_mem_cons.2 ⟨checked28_s21, List.forall_mem_cons.2 ⟨checked28_s22, List.forall_mem_cons.2 ⟨checked28_s23, List.forall_mem_cons.2 ⟨checked28_s24, List.forall_mem_cons.2 ⟨checked28_s25, List.forall_mem_cons.2 ⟨checked28_s26, List.forall_mem_cons.2 ⟨checked28_s27, List.forall_mem_cons.2 ⟨checked28_s28, List.forall_mem_cons.2 ⟨checked28_s29, List.forall_mem_cons.2 ⟨checked28_s30, List.forall_mem_cons.2 ⟨checked28_s31, List.forall_mem_cons.2 ⟨checked28_s32, List.forall_mem_cons.2 ⟨checked28_s33, List.forall_mem_singleton.2 checked28_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked28
