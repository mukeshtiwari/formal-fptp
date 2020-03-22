
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


class ring {A : Type*} (zero one : A) 
 (Radd Rsub Rmult : A → A → A) (Ropp : A → A) 
 [Hdec : decidable_eq A] := 
 (Habel : @abelian_group A zero Radd Ropp Hdec)
 (Hmon : @monoid A one Rmult Hdec)
 (Ring_distr_l : forall x y z, Rmult (Radd x y) z = Radd (Rmult x z) (Rmult y z))
 (Ring_distr_r : forall x y z, Rmult z (Radd x y) = Radd (Rmult z x) (Rmult z y))
 (Ring_sub_def : forall x y, Rsub x y = Radd x (Ropp y))


class field {A : Type*} (zero one : A) 
 (Fadd Fsub Fmult Fdiv : A → A → A) (Fopp Finv : A → A) 
 [Hdec : decidable_eq A] :=
 (Hnz : zero ≠ one)
 (Haddabel : @abelian_group A zero Fadd Fopp Hdec)
 (Hmulabel : @abelian_group A one Fmult Finv Hdec)
 (Field_sub_def : forall x y, Fsub x y = Fadd x (Fopp y))
 (Field_div_def : forall x y, Fdiv x y = Fmult x (Finv y))
 (Field_distr : forall x y z, Fmult x (Fadd y z) = Fadd (Fmult x y) (Fmult x z))





end AlgStructures