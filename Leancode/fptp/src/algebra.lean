
namespace AlgStructures

class monoid {A : Type*} (e : A) (f : A → A → A) [decidable_eq A]:=
 (Hassoc : ∀ a b c : A, f a (f b c) = f (f a b) c)
 (Hidl : ∀ a : A, f e a = a)
 (Hidr : ∀ a : A, f a e = a)


class group {A : Type*} (e : A) (f : A → A → A)
 (inv : A → A) [Hdec : decidable_eq A] := 
 (Hmon : @monoid A e f Hdec) 
 (Hinvl : ∀ x, f (inv x) x = e)
 (Hinvr : ∀ x, f x (inv x) = e)


class abelian_group {A : Type*} (e : A) (f : A → A → A)
 (inv : A → A) [Hdec : decidable_eq A] :=
 (Hg : @group A e f inv Hdec)
 (Hcomm : ∀ x y : A, f x y = f y x)

/- assuming a ring with identity -/
class ring {A : Type*} (zero one : A) 
 (Radd Rsub Rmult : A → A → A) (Ropp : A → A) 
 [Hdec : decidable_eq A] := 
 (Habel : @abelian_group A zero Radd Ropp Hdec)
 (Hmon : @monoid A one Rmult Hdec)
 (Ring_distr_l : forall x y z, Rmult (Radd x y) z = 
    Radd (Rmult x z) (Rmult y z))
 (Ring_distr_r : forall x y z, Rmult z (Radd x y) = 
    Radd (Rmult z x) (Rmult z y))
 (Ring_sub_def : forall x y, Rsub x y = Radd x (Ropp y))


class commutative_ring {A : Type*} (zero one : A) 
 (Radd Rsub Rmult : A → A → A) (Ropp : A → A) 
 [Hdec : decidable_eq A] :=
 (Hring : @ring A zero one Radd Rsub Rmult Ropp Hdec)
 (Hinv : forall x y : A, Rmult x y = Rmult y x)


class field {A : Type*} (zero one : A) 
 (Fadd Fsub Fmult Fdiv : A → A → A) (Fopp Finv : A → A) 
 [Hdec : decidable_eq A] :=
 (Hcring : @commutative_ring A zero one Fadd Fsub Fmult 
                Fopp Hdec)
 (Hfinvl : forall x : A, x ≠ zero -> Fmult (Finv x) x = one)
 (Hfinvr : forall x : A, x ≠ zero -> Fmult x (Finv x) = one)
 (Hzinv : Finv zero = zero)


class vector_space {F V : Type*} (Fzero Fone : F)
    (Fadd Fsub Fmult Fdiv : F → F → F) (Fopp Finv : F → F)
    (Vone : V) (Vdot : V → V → V) (Vinv : V → V) (Vop : F → V → V)
    [Hfdec : decidable_eq F] [Hgdec : decidable_eq V] :=
    (Hfield : @field F Fzero Fone Fadd Fsub Fmult Fdiv Fopp Finv Hfdec)
    (Hgroup : @abelian_group V Vone Vdot Vinv Hgdec)
    (Hcomp  : forall (x y : F) (v : V), Vop x (Vop y v) = Vop (Fmult x y) v)
    (Hdistr_fv : forall x v₁ v₂, Vop x (Vdot v₁ v₂) = Vdot (Vop x v₁) (Vop x v₂))
    (Hdistr_vf : forall x y v, Vop (Fadd x y) v = Vdot (Vop x v) (Vop y v))
    (Hfoneid : forall v, Vop Fone v = v)
    (Hfzerid : forall v, Vop Fzero v = Vone)


end AlgStructures

namespace Elgamal
open AlgStructures


def flip {A B : Type*} (f : A → B → B) := 
 λ (y : B) (x : A), f x y

 section
 variables 
   {F : Type*} 
   {G : Type*}
   (Fzero Fone : F)
   (Fadd Fsub Fmult Fdiv : F → F → F) 
   (Fopp Finv : F → F)
   (Gone : G) 
   (Gdot : G → G → G) 
   (Ginv : G → G) 
   (Gop : F → G → G)
   [Hfdec : decidable_eq F]
   [Hgdec : decidable_eq G]
   (g : G) /- generator -/
   (x : F) /- private key -/
   (h : G) /- publick key -/
   (Hp : h = flip Gop h x) /- g = h^x -/
   
/- When suppling Gdot, compute g^m -/
def elgamal_enc (m : G) (r : F) := 
  (flip Gop g r, Gdot m (flip Gop h r))



 
   

section

end Elgamal