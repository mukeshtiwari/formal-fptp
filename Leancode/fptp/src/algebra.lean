import 
  tactic.find tactic.omega 
  data.vector list_lemma



namespace AlgStructures


class monoid {A : Type*} (e : A) (f : A → A → A) [decidable_eq A] :=
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


class vector_space {F : Type*} {V : Type*} (Fzero Fone : F)
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
   [Hvec : @vector_space F G
           Fzero Fone Fadd 
           Fsub Fmult Fdiv
           Fopp Finv Gone 
           Gdot Ginv Gop 
           Hfdec Hgdec]

variables
   (g : G) /- generator -/
   (x : F) /- private key -/
   (h : G) /- publick key -/
   (Hp : h = Gop x g) /- g = h^x -/
   


/- When suppling Gdot, map m => g^m -/
def elgamal_enc (r : F) (m : G) := 
  (Gop r g, Gdot m (Gop r h))


def elgamal_dec (c : G × G) : G := 
 Gdot c.2 (Ginv (Gop x c.1))


def elgamal_reenc (r : F) (c : G × G) :=  
  (Gdot c.1 (Gop r g), Gdot c.2 (Gop r h))


def ciphertext_mult (c d : G × G) := 
     (Gdot c.1 d.1, Gdot c.2 d.2)


def vector_elegamal_enc {n : ℕ} :  
  vector F n -> vector G n ->  
  vector (G × G) n  
  | ⟨rs, Hr⟩ ⟨ms, Hm⟩ := 
    ⟨list.zip_with (elgamal_enc Gdot Gop g h) rs ms, 
    begin
      have Ht : list.length rs = list.length ms :=  
      begin rw [Hm, Hr] end, rw <- Hr, 
      apply zip_with_len_l, exact Ht
    end⟩


def vector_elegamal_dec {n : ℕ} :  
  vector (G × G) n -> vector G n  
  | ⟨cs, Hc⟩  := 
    ⟨list.map (elgamal_dec Gdot Ginv Gop x) cs, 
      by rw <- Hc; apply map_with_len_l⟩


def vector_elegamal_reenc {n : ℕ} :  
  vector F n -> vector (G × G) n ->  
  vector (G × G) n  
  | ⟨rs, Hr⟩ ⟨cs, Hc⟩ := 
    ⟨list.zip_with (elgamal_reenc Gdot Gop g h) rs cs, 
    begin 
      have Ht : list.length rs = list.length cs :=  
      begin rw [Hc, Hr] end,
      rw <- Hr, apply zip_with_len_l, exact Ht 
    end⟩


def vector_ciphertext_mult {n : ℕ} :  
  vector (G × G) n -> vector (G × G) n -> 
  vector (G × G) n  
  | ⟨cs₁ , Hc₁⟩  ⟨cs₂, Hc₂⟩ := 
    ⟨list.zip_with (ciphertext_mult Gdot) cs₁  cs₂, 
    begin 
      have Ht : list.length cs₁ = list.length cs₂ :=  
      begin rw [Hc₁, Hc₂] end,
      rw <- Hc₁, apply zip_with_len_l, exact Ht,
    end⟩


include Hvec Hp
theorem decryption_correct (r : F) (m : G) (c : G × G):
  c = elgamal_enc Gdot Gop g h r m -> 
  elgamal_dec Gdot Ginv Gop x c = m :=
begin
  intro Hc, rw [Hc, Hp],  
  unfold elgamal_enc elgamal_dec,
  simp, 
  destruct Hvec, intros, clear a, 
  repeat {rw Hcomp}, 
  destruct Hgroup, intros, clear a, 
  destruct Hfield, intros, clear a, 
  destruct Hcring, intros, clear a, 
  rw Hinv, 
  destruct Hring, intros, clear a, 
  destruct Hg, intros, clear a, 
  destruct Hmon_1, intros, clear a, 
  rw [<- Hassoc, Hinvr, Hidr]
end

theorem reencryption_decrypt_correct 
  (r₁ r₂ : F) (m : G) (c₁ c₂ : G × G) :
  c₁ = elgamal_enc Gdot Gop g h r₁ m    -> 
  c₂ = elgamal_reenc Gdot Gop g h r₂ c₁ ->
  elgamal_dec Gdot Ginv Gop x c₂ = m :=
  begin 
    intros Hc₁ Hc₂, 
    rw [Hc₂, Hc₁, Hp],
    unfold elgamal_dec 
      elgamal_reenc elgamal_enc,
    simp, sorry
  end 

theorem ciphertext_mult_homomorphic 
  (r₁ r₂ : F) (m₁ m₂ : G) (c₁ c₂ c₃ : G × G) :
  c₁ = elgamal_enc Gdot Gop g h r₁ m₁ -> 
  c₂ = elgamal_enc Gdot Gop g h r₂ m₂ ->
  c₃ = ciphertext_mult Gdot c₁ c₂     -> 
  elgamal_dec Gdot Ginv Gop x c₃ = Gdot m₁ m₂ :=
  begin 
    intros Hc₁ Hc₂ Hc₃,
    rw [Hc₃, Hc₂, Hc₁, Hp],
    unfold elgamal_enc
      ciphertext_mult elgamal_dec, 
    simp, /- feed to sat solver-/
    sorry    
  end 
 
   

end 
end Elgamal