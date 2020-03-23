import data.zmod.basic data.nat.prime 
  data.zmod.quadratic_reciprocity
  tactic.find tactic.omega data.vector
  list_lemma

namespace ElGamal 
/- 
A Schnorr group is a large prime-order subgroup of ℤ∗𝑝, 
the multiplicative group of integers modulo 𝑝. 
To generate such a group, we find 𝑝=𝑞𝑟+1 such that 𝑝 and 𝑞
are prime. Then, we choose any ℎ
in the range 1<ℎ<𝑝 such that ℎ^r ≠ 1 (mod𝑝)
The value 𝑔=ℎ^𝑟(mod𝑝) is a generator of a subgroup ℤ∗𝑝 of order 𝑞.
By Fermat's little theorem
g^q = h^(rq) = h^(p-1) = 1 (mod p)
-/

variables
  (p : ℕ) (q : ℕ) (r : ℕ)
  (Hr : 2 ≤ r)
  (Hp : nat.prime p)
  (Hq : nat.prime q)
  (Hdiv : p = q * r + 1)
  (h : zmodp p Hp) 
  (Hh₁ : h ≠ 0)
  (Hh₂ : h^r ≠ 1)
  (g : zmodp p Hp) /- generator of a subgroup of ℤ⋆p of order q -/
  (Hg : g = h^r)
  
section 
include Hg Hdiv Hh₁ 
theorem generator_proof : g ^ q = 1 := 
begin 
  rw [Hg, <- pow_mul, mul_comm],
  have Ht : p - 1 = q * r := nat.pred_eq_of_eq_succ Hdiv,
  rw <- Ht, exact zmodp.fermat_little Hp Hh₁
end
end


variables 
  (prikey : zmodp q Hq) /- private key -/
  (pubkey : zmodp p Hp) /- public key -/
  (Hrel : pubkey = g^prikey.val)


def elgamal_enc (m : zmodp p Hp) (r : zmodp q Hq) := 
  (g^r.val, g^m.val * pubkey^r.val)

def elgamal_dec (c : zmodp p Hp ×  zmodp p Hp) := 
  c.2 * (c.1^prikey.val)⁻¹ 

def elgamal_reenc (c : zmodp p Hp ×  zmodp p Hp) 
  (r : zmodp q Hq) :=  
  (c.1 * g^r.val, c.2 * pubkey^r.val)

def ciphertext_mult (c : zmodp p Hp × zmodp p Hp)
     (d : zmodp p Hp ×  zmodp p Hp) := 
     (c.1 * d.1, c.2 * d.2)


def vector_elegamal_enc {n : ℕ} :  
  vector (zmodp p Hp) n -> vector (zmodp q Hq) n -> 
  vector (zmodp p Hp × zmodp p Hp) n  
  | ⟨ms, Hm⟩  ⟨rs, Hr⟩ := 
    ⟨list.zip_with (elgamal_enc p q Hp Hq g pubkey) ms rs, 
    begin
      have Ht : list.length ms = list.length rs :=  
      begin rw [Hm, Hr] end,
      rw <- Hm, apply zip_with_len_l, exact Ht
    end ⟩

def vector_elegamal_dec {n : ℕ} :  
  vector (zmodp p Hp × zmodp p Hp) n -> 
  vector (zmodp p Hp) n  
  | ⟨cs, Hc⟩  := 
    ⟨list.map (elgamal_dec p q Hp Hq prikey) cs, 
    begin 
      rw <- Hc, apply map_with_len_l, 
    end ⟩

def vector_elegamal_reenc {n : ℕ} :  
  vector (zmodp p Hp × zmodp p Hp) n -> vector (zmodp q Hq) n -> 
  vector (zmodp p Hp × zmodp p Hp) n  
  | ⟨cs, Hc⟩  ⟨rs, Hr⟩ := 
    ⟨list.zip_with (elgamal_reenc p q Hp Hq g pubkey) cs rs, 
    begin 
      have Ht : list.length cs = list.length rs :=  
      begin rw [Hc, Hr] end,
      rw <- Hc, apply zip_with_len_l, exact Ht
    end ⟩


def vector_ciphertext_mult {n : ℕ} :  
  vector (zmodp p Hp × zmodp p Hp) n -> vector (zmodp p Hp × zmodp p Hp) n -> 
  vector (zmodp p Hp × zmodp p Hp) n  
  | ⟨cs₁ , Hc₁⟩  ⟨cs₂, Hc₂⟩ := 
    ⟨list.zip_with (ciphertext_mult p Hp) cs₁  cs₂, 
    begin 
      have Ht : list.length cs₁ = list.length cs₂ :=  
      begin rw [Hc₁, Hc₂] end,
      rw <- Hc₁, apply zip_with_len_l, exact Ht,
    end ⟩

/-
inductive count 

1. a ballot encrypted with [g^0, g^0, ....]
2. a ballot is valid add it to the running margin
3. invalid, discard it and permute it by 
    a secret permutation 
4. when no more ballot left, then honest decryption

Zero-Knowledge-Proof framework

Wikstrom Shuffle proof
Extend it to the Coq as well, plug these 
proofs in Coq. 

-/
      

include Hrel Hg Hh₁ 
theorem elgama_enc_dec_identity :  
∀ m r', elgamal_dec p q Hp Hq prikey 
       (elgamal_enc p q Hp Hq g pubkey m r') = g^m.val := 
begin
  unfold elgamal_enc elgamal_dec,
  intros, simp, rw [Hrel, <- pow_mul, <- pow_mul],
  have Ht : g ≠ 0 := begin 
  rw Hg, exact pow_ne_zero r Hh₁ end,
  have Ht₁ : g ^ (prikey.val * r'.val) ≠ 0 := 
    pow_ne_zero _ Ht,
  have Ht₂ : r'.val * prikey.val = prikey.val * r'.val := 
       mul_comm r'.val prikey.val,
  rw [Ht₂, mul_assoc, mul_inv_cancel Ht₁], ring  
end


theorem additive_homomorphic_property : forall c d m₁ m₂ r₁ r₂,
 c = elgamal_enc p q Hp Hq g pubkey m₁ r₁ ->
 d = elgamal_enc p q Hp Hq g pubkey m₂ r₂ -> 
 (g^(r₁.val + r₂.val), g^(m₁.val + m₂.val) * 
 pubkey^(r₁.val + r₂.val)) = ciphertext_mult p Hp c d := 
begin 
  unfold elgamal_enc ciphertext_mult, 
  intros c d m₁ m₂ r₁ r₂ Hc Hd, simp,
  have Ht₁ : g ^ (r₁.val + r₂.val) = c.fst * d.fst := 
  begin 
    rw [Hc, Hd], simp, exact pow_add g r₁.val r₂.val
  end,
  have Ht₂ : g ^ (m₁.val + m₂.val) * pubkey ^ (r₁.val + r₂.val) = 
      c.snd * d.snd :=  begin
        rw [Hc, Hd, pow_add, 
        pow_add], simp, ring
        end,
  exact and.intro Ht₁ Ht₂
end






end ElGamal

#check ElGamal.elgamal_enc 